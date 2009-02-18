(ns edu.berkeley.ai.angelic.hierarchies.strips-hierarchies
  (:refer-clojure)
  (:use [edu.berkeley.ai.angelic :as angelic] 
        [edu.berkeley.ai.angelic.hierarchies :as hierarchies])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
        [edu.berkeley.ai.util.propositions :as props]
        [edu.berkeley.ai.domains.strips :as strips]
        [edu.berkeley.ai.angelic.ncstrips-descriptions :as ncstrips]
	[edu.berkeley.ai.search.smart-csps :as smart-csps]
        )
  )

;;; A strips-like hierarchy definition, essentially the one used in our ICAPS '07 and '08 papers.

; Immediate refinements are [name pos-prec neg-prec unk-types expansion]
;; TODO: when instantiated, change unk-types to unk-domains

; TODO: change over to use conditions everywhere? (and add propositional-condition)

;; HLA schemata

(defstruct strips-hla-schema :class :name :vars :pos-pre :neg-pre :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)

(defn make-strips-hla-schema [name parameters pos-preconditions neg-preconditions refinement-schemata optimistic-schema pessimistic-schema primitive]
  (struct strips-hla-schema ::StripsHLASchema name parameters pos-preconditions neg-preconditions 
	  refinement-schemata optimistic-schema pessimistic-schema primitive))

(def *noop-strips-hla-schema* 
     (make-strips-hla-schema (gensym "noop") nil nil nil nil *identity-description* *identity-description* :noop))

; TODO: double check about removing precs from NCSTRIPS for primitives.
; TODO: some more general way to do this (without focusing on ncstrips)
(defn- make-strips-primitive-hla-schema [types objects predicates action]
  (let [desc (ncstrips/make-ncstrips-description-schema 
	      types (props/check-objects types (concat objects (:vars action))) predicates 
	      [(ncstrips/make-ncstrips-effect-schema nil nil nil ; (:pos-pre action) (:neg-pre action) TODO: double check
					      (:add-list action) (:delete-list action) nil nil nil nil nil (constantly (:cost action)))] 
	      (:vars action))]
    (make-strips-hla-schema (:name action) (:vars action) (:pos-pre action) (:neg-pre action) 
			    :primitive desc desc action)))


(defn parse-strips-hla-schema [hla domain]
  (util/match [#{[:optional [:parameters   ~parameters]]
	    [:optional [:precondition ~precondition]]
	    [:multiple [:refinement   ~refinements]]
	    [:optional [:optimistic   ~optimistic]]
	    [:optional [:pessimistic  ~pessimistic]]
	    [:optional [:exact        ~exact]]}
	  (util/partition-all 2 (rest hla))]
    (when exact (util/assert-is (empty? optimistic)) (util/assert-is (empty? pessimistic)))
    (let [name (first hla)
	  [pos-pre neg-pre] (props/parse-pddl-conjunction precondition)
	   params        (props/parse-typed-pddl-list parameters)] 
      (make-strips-hla-schema
       name
       params
       pos-pre
       neg-pre
       (map (fn [refinement]
	      (util/match [[[:optional [:name ~ref-name]]
			    [:optional [:parameters ~parameters]]
			    [:optional [:precondition ~precondition]]
			    [:expansion ~expansion]]
			   (util/partition-all 2 refinement)]
		(let [[pp np] (props/parse-pddl-conjunction precondition)]
		  [(if ref-name (util/symbol-cat name '- ref-name) (gensym name)) pp np 
		   (util/map-map (fn [[x y]] [y x]) (props/parse-typed-pddl-list parameters)) 
		   (or (seq expansion) (list (list (:name *noop-strips-hla-schema*))))])))
	    refinements)
       (parse-description (or optimistic exact [:opt]) domain params)
       (parse-description (or pessimistic exact [:pess]) domain params)
       nil))))


(defn- check-hla-expansion [types vars-and-objects all-actions expansion]
  (doall
  (for [action expansion]
    (do 
      (let [params (rest action)
	    declared-types (util/safe-get all-actions (first action))]
	(util/assert-is (= (count params) (count declared-types)))
	(doseq [[type par] (map vector declared-types params)]
	  (props/check-type types vars-and-objects par type)))      
      (vec action)))))

(comment  ; TODO: fix this up when actually using union types
(defn get-dummy-var-type-map [types all-actions declared-types expansion]
  (util/map-vals #(props/maximal-subtypes types %)
    (reduce 
     (fn [type-map [var type]]
       (if (contains? type-map var)
	   (util/assoc-cons type-map var type)
         type-map))
     (util/map-map (fn [[t v]] [v [t]]) declared-types)
     (util/forcat [action expansion]
       (map vector (rest action) (util/safe-get all-actions (first action)))))))
   )

(defn- check-hla-schema [types guaranteed-objs predicates all-actions hla-schema] 
  (util/assert-is (contains? #{nil :noop} (util/safe-get hla-schema :primitive)))
  (util/assert-is (not (map? (:vars hla-schema))))
  (util/assert-is (util/distinct-elts? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
  (let [vars-and-objects (props/check-objects types (concat guaranteed-objs (:vars hla-schema)))
	atom-checker     (fn [atoms] (map #(props/check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-hla-schema 
     (:name hla-schema)
     (:vars hla-schema)
     (atom-checker (:pos-pre hla-schema))
     (atom-checker (:neg-pre hla-schema))
     (doall 
     (map (fn [[name pos-pre neg-pre dummy-map expansion]]
	    (let [impl-vars-and-objects (reduce (fn [m [v t]] (util/assoc-cons m t v)) vars-and-objects dummy-map) 
		  impl-atom-checker (fn [atoms] (map #(props/check-atom types impl-vars-and-objects predicates %) atoms))]
;	      (prn (:name hla-schema) dummy-map)
	      [name
	       (impl-atom-checker pos-pre)
	       (impl-atom-checker neg-pre)
	       dummy-map
	       (check-hla-expansion 
		types 
		impl-vars-and-objects
		all-actions 
		expansion)]))
	  (:refinement-schemata hla-schema)))
     (:optimistic-schema hla-schema)
     (:pessimistic-schema hla-schema)
     (:primitive hla-schema))))

(defn- check-hla-schemata [types guaranteed-objs predicates actions hla-schemata]
;  (prn hla-schemata)
  (let [all-actions (merge (util/map-map #(vector (:name %) (map first (:vars %))) actions)
			   (util/map-map #(vector (:name %) (map first (:vars %))) hla-schemata))]
;    (prn all-actions)
    (util/assert-is (= (count all-actions) (+ (count actions) (count hla-schemata))))
    (let [hla-schemata (doall (map #(check-hla-schema types guaranteed-objs predicates all-actions %) hla-schemata))]
      (util/assert-is (some #(= (:name %) 'act) hla-schemata))
      (util/map-map #(vector (:name %) %) 
	       (concat hla-schemata
		       (map #(make-strips-primitive-hla-schema types guaranteed-objs predicates %) actions))))))



;; Parse and check an entire hierarchy   
     
(defmethod parse-hierarchy-type :strips-hierarchy [type contents domain]
  (util/assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (util/match [[[:multiple (:hla ~@hlas)]] contents]
    {:class ::StripsHierarchySchema, :hlas
     (check-hla-schemata (:types domain) (:guaranteed-objs domain) (:predicates domain) (:action-schemata domain)
			 (cons *noop-strips-hla-schema* (map #(parse-strips-hla-schema % domain) hlas)))}))

(defn make-flat-act-optimistic-description-schema [upper-reward-fn]
  {:class ::FlatActOptimisticDescriptionSchema :upper-reward-fn upper-reward-fn})

(defmethod instantiate-description-schema ::FlatActOptimisticDescriptionSchema [desc instance]
  (make-flat-act-optimistic-description (envs/get-goal instance) (:upper-reward-fn desc)))

(defmethod ground-description :edu.berkeley.ai.angelic.hierarchies/FlatActOptimisticDescription [desc var-map] desc)


; TODO: use ncstrips for Act description?
; Immediate refinements are [name pos-prec neg-prec unk-types expansion]
; TODO: check it's correct to ignore primitive precs.
(defn make-flat-strips-hierarchy-schema [domain upper-reward-fn]
  (util/assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  {:class ::StripsHierarchySchema
   :hlas 
     (util/map-map #(vector (:name %) %) 
       (cons *noop-strips-hla-schema*
	(cons
	  (make-strips-hla-schema
	   'act nil nil nil
	   (cons ['empty nil nil nil [[(util/safe-get *noop-strips-hla-schema* :name)]]]
		 (for [action (:action-schemata domain)]
		   (let [dummy-vars (for [[t v] (:vars action)] [(keyword (str "?" v)) t])]
		     [(:name action) nil nil (into {} dummy-vars) [(into [(:name action)] (map first dummy-vars)) ['act]]])))
	   (make-flat-act-optimistic-description-schema upper-reward-fn)
	   *pessimal-description* nil)
	  (map #(make-strips-primitive-hla-schema 
                 (:types domain) (:guaranteed-objs domain) (:predicates domain) %)
	       (:action-schemata domain)))))})



(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )





;; Grounded STRIPS HLAs and hierarchies (here, actual grounding done JIT)
; Immediate refinements are [name pos-prec neg-prec CSP (not unk-types) expansion !!!]

(derive ::StripsHLA :angelic.hierarchies/HLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)
(derive ::StripsNoopHLA ::StripsPrimitiveHLA)


(defstruct strips-hierarchy :class :hla-map :problem-instance)

(defstruct strips-hla :class :hierarchy :schema :var-map :precondition)

(defn make-strips-hla [hierarchy schema var-map precondition primitive]
  (struct strips-hla 
	  (cond (= primitive :noop) ::StripsNoopHLA primitive ::StripsPrimitiveHLA :else ::StripsHLA)
	  hierarchy schema var-map precondition))



;; pulls all ***constant*** constraints from refinement, not just first action? 
(defn extract-preconditions [var-map action-inst hla-map] "Returns [pos neg]"
  (let [[act-name & args] action-inst
	hla (util/safe-get hla-map act-name)
	trans-var-map (translate-var-map hla args var-map)
	simplifier #(props/simplify-atom trans-var-map %)]
    ;(println act-name (:pos-pre hla) (:neg-pre hla))
    [(map simplifier (:pos-pre hla))
     (map simplifier (:neg-pre hla))]))
	
; This is needed because constant-simplified strips primtitive schemata are in-between full schemata and instances.
(defn- constant-simplify-strips-primitive-schema [primitive const-preds]
  (reduce (fn [m f] (assoc m f (remove #(const-preds (first %)) (util/safe-get m f))))
	  primitive [:pos-pre :neg-pre :add-list :delete-list]))

; CSP takes on sole responsibility for handling *all* constant predicates.  Really (?)
; TODO: drop all constants here!  BUT must do it in right order?
(defn- instantiate-strips-hla-schema [schema instance hla-map trans-objects const-pred-map]
  (let [{:keys [name vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	const-preds  (util/keyset const-pred-map)
	deconst      (fn [atoms] (remove #(const-preds (first %)) atoms))]
    (make-strips-hla-schema 
     name vars (deconst pos-pre) (deconst neg-pre)
     (or (and (not (coll? refinement-schemata)) refinement-schemata)
      (doall
       (for [[r-name pos-prec neg-prec dummy-type-map expansion] refinement-schemata]   
	 (let [arg-val-map   (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
	       dummy-val-map (get-dummy-var-val-map trans-objects dummy-type-map)
	       var-map      (into {} (map #(vector % %) (concat (map second vars) (map first dummy-type-map))))
	       [all-pos-pre all-neg-pre]
	          (map concat
		    [pos-prec neg-prec]
                    (extract-preconditions var-map (first expansion) hla-map)
		    (map (fn [precs] (filter #(const-preds (first %)) precs))
		       (apply map concat [nil nil]
			 (map #(extract-preconditions var-map % hla-map)
			      (rest expansion)))))]
	   (util/assert-is (not (empty? expansion)))
;	   (print "Constructing CSP for " name " " r-name ": " );(set all-pos-pre) (set all-neg-pre)) 
	   [r-name (deconst pos-prec) (deconst neg-prec) 
	    (smart-csps/create-smart-csp (set all-pos-pre) (set all-neg-pre) arg-val-map dummy-val-map const-pred-map)
	    expansion]))))
     (instantiate-description-schema optimistic-schema instance)
     (instantiate-description-schema pessimistic-schema instance)
     (if (or (not primitive) (= primitive :noop)) primitive  ; TODO: hacky.
	 (constant-simplify-strips-primitive-schema primitive const-preds)))))



(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (let [old-hla-map    (util/safe-get hierarchy :hlas)
	act-vars       (util/safe-get-in old-hla-map 'act :vars)
	root-hla-name  (gensym "strips-top-level-action")
	old-hla-map    (assoc old-hla-map root-hla-name
			 (make-strips-hla-schema root-hla-name [] nil nil 
			   [["act" nil nil (util/map-map (fn [[t v]] [v t]) act-vars) 
			     (into '[act] (map second act-vars))]]
			   (parse-description [:opt] :dummy :dummy)
			   (parse-description [:pess] :dummy :dummy)
			   nil))
	trans-objects  (util/safe-get instance :trans-objects)
	const-pred-map (:const-pred-map instance)
	new-hla-map    (util/map-vals 
			#(instantiate-strips-hla-schema % instance old-hla-map trans-objects const-pred-map)
			old-hla-map)]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy new-hla-map instance)
     (util/safe-get new-hla-map root-hla-name)
     {}
     envs/*true-condition*
     false)))    




(comment 
  (instantiate-hierarchy
   (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		    (make-nav-switch-strips-domain))
   (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))

		    )


;; HLA methods
    
(defmethod hla-environment ::StripsHLA [hla] (util/safe-get (util/safe-get hla :hierarchy) :problem-instance))

(defmethod hla-name                       ::StripsHLA [hla] 
  (into [(:name (:schema hla))]
	(replace (:var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive? ::StripsHLA [hla] false)
(defmethod hla-primitive ::StripsHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-primitive? ::StripsPrimitiveHLA [hla] true) 
(defmethod hla-primitive ::StripsPrimitiveHLA [hla] 
  (strips/strips-action->action (strips/get-strips-action-schema-instance (:primitive (:schema hla)) (:var-map hla))))

(defmethod hla-primitive? ::StripsNoopHLA [hla] true) 
(defmethod hla-primitive ::StripsNoopHLA [hla] :noop) 


(defmethod hla-hierarchical-preconditions ::StripsHLA [hla]  (:precondition hla))

(defmethod hla-optimistic-description     ::StripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (:var-map hla)))
  
(defmethod hla-pessimistic-description    ::StripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (:var-map hla)))



(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map]
  (let [hla-vars (:vars hla)]
    (loop [ret {}, args (seq args), vars (seq (:vars hla))]
      (util/assert-is (not (util/xor args vars)))
      (if (not args) ret
	(recur (assoc ret (second (first vars)) (util/safe-get var-map (first args)))
	       (rest args) (rest vars))))))

(defn- get-dummy-var-val-map [objects dummy-var-type-map]
  (util/map-vals (fn [t] (util/safe-get objects t)) dummy-var-type-map)) 


(defmethod hla-immediate-refinements [::StripsPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-immediate-refinements     [::StripsHLA :edu.berkeley.ai.angelic/PropositionalValuation] [hla opt-val]
  (let [opt-val      (restrict-valuation opt-val (:precondition hla))
	var-map      (:var-map hla)	
	hierarchy    (:hierarchy hla)
	precondition (:precondition hla)
	hla-map      (:hla-map hierarchy)]
    (when-not (empty-valuation? opt-val)
      (let [val-pred-maps (valuation->pred-maps opt-val)]
  	  (for [[name pos-pre neg-pre csp expansion] (:refinement-schemata (:schema hla))
	        dummy-var-map (smart-csps/get-smart-csp-solutions csp var-map val-pred-maps)]
	    (let [final-var-map (merge var-map dummy-var-map)
		  simplifier #(props/simplify-atom final-var-map %)
		  ground-impl-pre (envs/make-conjunctive-condition
				   (map simplifier pos-pre)
				   (map simplifier neg-pre))]
	      (map (fn [call extra-preconditions]
		     (let [hla (util/safe-get hla-map (first call))
			   trans-var-map (translate-var-map hla (rest call) final-var-map)
 	   		   simplifier #(props/simplify-atom trans-var-map %)
			   precond 
			   (envs/conjoin-conditions 
			    (envs/make-conjunctive-condition
			     (map simplifier (util/safe-get hla :pos-pre)) 
			     (map simplifier (util/safe-get hla :neg-pre))) 
			    extra-preconditions)]
		       (make-strips-hla hierarchy hla trans-var-map precond (:primitive hla)))) 
		   expansion
		   (cons (envs/conjoin-conditions precondition ground-impl-pre)
			 (repeat envs/*true-condition*)))))))))

(comment 
  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (constant-simplify-strips-hierarchy (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env) constant-predicate-simplify-strips-planning-instance))] (count node))


  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (constant-simplify-strips-hierarchy (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env) constant-predicate-simplify-strips-planning-instance))] (count node))


 ;(time (second (a-star-search node))))
  )
	      















;;; Fully grounded and constant-simplified strips hierarchies 	

; can't fully fully bottom out because of hierarchical preconditions!?!??!?
; ref-fn should automagically handle hierarchical preconds . . . takes grounded-hla and valuation as args.
; Immediate refinements are [name pos-prec neg-prec unk-types expansion]

; refs in :refs are [precondition expansion-names]
; ref-fn must process these.


; TODO: just change to JIT grounder?

;;; TODO: de-uglify this to re-use above work
; Issues: would like access to fluent preconditions (can provide this service from CSPs).

;(defstruct strips-hierarchy :class :hla-map :problem-instance)

;(defstruct strips-hla :class :hierarchy :schema :var-map :precondition)

;(defn make-strips-hla [hierarchy schema var-map precondition primitive]
;  (struct strips-hla 
;	  (cond (= primitive :noop) ::StripsNoopHLA primitive ::StripsPrimitiveHLA :else ::StripsHLA)
;	  hierarchy schema var-map precondition))


; Immediate refinements are [name pos-prec neg-prec csp expansion]

;(defstruct strips-hla-schema :class :name :vars :pos-pre :neg-pre :refinement-schemata :optimistic-schema :pessimistic-;schema :primitive)

;; TODO: ref generator should replace prec. of first action with that of ref.

;; TODO: just call hla-immediate-refinements!

;(defn- make-grounded-strips-hla-schema [env name precondition refs ref-fn opt-desc pess-desc primitive]


(defstruct grounded-strips-hla-schema :class :env :name :precondition :refs :ref-fn :opt-desc :pess-desc :primitive) ; TODO: remove refs?

(defn- make-grounded-strips-hla-schema [env name precondition refs ref-fn opt-desc pess-desc primitive]
  (struct grounded-strips-hla-schema ::GroundedStripsHLASchema 
    env name precondition refs ref-fn opt-desc pess-desc primitive))

(defn- make-grounded-strips-noop-schema [env]
     (make-grounded-strips-hla-schema env
      (list (util/safe-get *noop-strips-hla-schema* :name)) envs/*true-condition* 
      :noop #(throw (UnsupportedOperationException.)) *identity-description* *identity-description* :noop))

(defstruct grounded-strips-hla :class :hla-map :schema :hierarchical-precondition)

(defn- make-grounded-strips-hla [hla-map schema hierarchical-precondition]
  (struct grounded-strips-hla ::GroundedStripsHLA hla-map schema hierarchical-precondition))


(defn ground-strips-hierarchy [hla]
  (util/assert-is (= (:class hla) ::StripsHLA))
  (let [{:keys [hierarchy schema var-map precondition primitive]} hla
	instance       (util/safe-get hierarchy :problem-instance)
	hla-map        (HashMap. (util/safe-get hierarchy :hla-map))]
    (make-grounded-strips-hla hla-map schema
    (util/make-safe (put-grounded-hlas root-action-name {} instance old-hla-map new-hla-map))
    (doseq [[k v] (doall (seq new-hla-map))] (when (util/includes? [:on-stack :bad] (first v)) (.remove new-hla-map k)))
    (println "Number of grounded actions: " (count (keys new-hla-map)))
    (make-grounded-strips-hla
     new-hla-map 
     (util/safe-get new-hla-map (list root-action-name))
     envs/*true-condition*)))
  

; input refs are [precondition expansion-names]
; output refs, seqs of grounded-strips-hal,  (given grounded-strips-hla and optimistic-valuations)
; Keep in mind, high-level precondition of first action already taken into account!
  ; TODO: no-op for empty refinement!
 ; For now, do simplest stupid thing. TODO: improve!

(defn- make-refinement-generator
  ([refs] (let [real-fn (make-refinement-generator refs #{})]
	    (fn [hla opt-val]
	      (util/assert-is (isa? (:class opt-val) :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation))
	      (let [hla-map (util/safe-get hla :hla-map)
		    allowed-refs (distinct (mapcat real-fn (util/safe-get opt-val :dnf)))] 
		(for [exp allowed-refs]
;		  (when (seq exp)
		    (cons (let [first-schema (util/safe-get hla-map (first exp))]
			    (make-grounded-strips-hla 
			     hla-map first-schema  
			     (envs/conjoin-conditions (util/safe-get hla :hierarchical-precondition) (util/safe-get first-schema :precondition))))
			  (for [act (rest exp)]
			    (let [schema (util/safe-get hla-map act)]
			      (make-grounded-strips-hla hla-map schema (util/safe-get schema :precondition))))))))))
  ([refs blacklist]
   (let [most-common-pair
  	  (first 
	    (util/maximal-elements second
	      (util/merge-reduce + {}
	        (map #(vector % 1)
                  (apply concat
                    (for [ref refs]
		      (remove #(contains? blacklist %) (concat (:pos (first ref)) (:neg (first ref))))))))))]
    (if (nil? most-common-pair) 
        (fn [clause] (map second refs))
      (let [most-common-atom (first most-common-pair)
	    ref-map
	      (util/group-by
	        (fn [ref]
	          (let [in-pos? (util/includes? (:pos (first ref)) most-common-atom)
			in-neg? (util/includes? (:neg (first ref)) most-common-atom)]
	  	    (cond (and in-pos? in-neg?) (do (prn "Warning: contradictory preconditions for ref" ref) 
						  :trash)
			  (and in-pos? (not in-neg?)) :positive
			  (and in-neg? (not in-pos?)) :negative
			  :else                       :dontcare)))
		refs)
	    {pos-refs :positive neg-refs :negative dc-refs :dontcare} ref-map
	    next-blacklist (conj blacklist most-common-atom)
	    pos-branch (if pos-refs (make-refinement-generator pos-refs next-blacklist) (constantly nil))
	    neg-branch (if neg-refs (make-refinement-generator neg-refs next-blacklist) (constantly nil))
	    dc-branch  (if dc-refs  (make-refinement-generator dc-refs  next-blacklist) (constantly nil))]
	(fn [clause]
	  (let [val (get clause most-common-atom)]
	    (concat 
	     (cond (= val :true) (pos-branch clause)
		   (nil? val)    (neg-branch clause)
		   :else         (concat (pos-branch clause) (neg-branch clause)))
	     (dc-branch clause)))))))))



  

(defn get-grounded-refinement-schema-instantiations [ref-schema var-map old-hla-map new-mutable-hla-map pred-maps]
  (let [[_ _ _ csp expansion] ref-schema]
    (doall
     (filter identity
      (for [unk-map (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
        (let [final-map      (merge var-map unk-map)
	      grounder       #(cons (first %) (props/simplify-atom final-map (rest %)))
	      vm-translator  #(translate-var-map (util/safe-get old-hla-map (first %)) (rest %) final-map)]
	  (when (every? #(put-grounded-hlas (first %) (vm-translator (first %)) old-hla-map new-mutable-hla-map pred-maps)
			expansion)
	    [(envs/make-conjunctive-condition 
			       (set (map grounder (smart-csp-pos-fluent-constraints)))
			       (set (map grounder (smart-csp-neg-fluent-constraints))))
	     (map grounder expansion)))))))))

(comment 
(defn constant-simplify-strips-action [action true-atoms false-atoms]
  (util/assert-is (nil? (util/safe-get action :vars)))
  (let [pos-pre    (util/difference (util/to-set (util/safe-get action :pos-pre)) true-atoms)
        neg-pre    (util/difference (util/to-set (util/safe-get action :neg-pre)) false-atoms)]
    (when (and (empty? (util/intersection pos-pre false-atoms))
               (empty? (util/intersection neg-pre true-atoms)))
      (strips/make-strips-action-schema 
       (util/safe-get action :name)
       nil
       pos-pre
       neg-pre
       (util/safe-get action :add-list)
       (util/safe-get action :delete-list)
       (util/safe-get action :cost))))) 
 )


(import '(java.util HashMap))
(declare put-grounded-hlas)

(defn put-grounded-hlas [strips-hla instance #^HashMap new-mutable-hla-map dummy-valuation]
  (let [{:keys [hierarchy schema var-map precondition]} strips-hla
	full-name (hla-name strips-hla)
	old-val   (.get new-mutable-hla-map full-name)]
    (cond (= old-val :bad)   false
	  (= old-val :stack) true
	  :else
      (let [opt  (hla-optimistic-description strips-hla)
	    pess (hla-pessimistic-description strips-hla)]
        (if (hla-primitive? strips-hla)
	    (do  
	      (.put new-mutable-hla-map full-name
		(make-grounded-strips-hla-schema instance full-name precondition #(throw (UnsupportedOperationException.))
						 opt pess (hla-primitive strips-hla))) ;todo: simplify prim?
	      true)
	  (do 
	    (.put new-mutable-hla-map full-name :stack)
	    (let [strips-hla (assoc strips-hla :precondition nil)
		  refs
		   (doall
		    (filter 
		     (fn [ref] (every? #(put-grounded-hlas % instance new-mutable-hla-map dummy-valuation) ref)) 
		     (hla-immediate-refinements strips-hla dummy-valuation)))]
	      (if refs 
		  (do 
		    (.put new-mutable-hla-map full-name
 		      (make-grounded-strips-hla-schema instance full-name precondition (make-refinement-generator refs)
						       opt pess false))
		    true)
		(do
		  (.put new-mutable-hla-map full-name :bad)
		  false)))))))))
		
	      

;; Blank out precondition;
  

; Puts this action and descendents into new-hla-map, returning
; true for success or nil for "bad action" (or no refs.)
; Do braindead way for now, speed up later.
; TODO: should really check cycles better, to get rid of things with only infinite refinements.
; Are we even handling refinement preconditions???
; TODO: special case, top-level should match only against initial state ????
	    (when-let [refs 
		       (doall 
			(filter identity
			      (for [ref-schema refinement-schemata
				    full-var-map (get-possible-ref-schema-var-maps ref-schema 
						   var-map trans-objects always-true-atoms always-false-atoms)]
				(do ;(prn "try " ref-schema full-var-map)
				(get-grounded-refinement-schema-instantiation 
				 ref-schema full-var-map instance old-hla-map new-mutable-hla-map)))))]
;	      (prn "step3")
	      (.put new-mutable-hla-map full-name		    
		    (make-grounded-strips-hla-schema instance
		     full-name new-precondition refs (make-refinement-generator refs) opt-desc pess-desc nil))
	      true)))]
	  result
	 (do (.put new-mutable-hla-map full-name [:bad]) false))))))


     
(defn ground-and-constant-simplify-strips-hierarchy [hla instance-simplifier]
  (util/assert-is (= (:class hla) ::StripsHLA))
  (let [old-hierarchy      (util/safe-get hla :hierarchy)
	root-action-name   (util/safe-get (util/safe-get hla :schema) :name)
	old-hla-map        (util/safe-get old-hierarchy :hla-map)
	instance           (instance-simplifier (util/safe-get old-hierarchy :problem-instance))
	noop-schema        (make-grounded-strips-noop-schema instance)
	new-hla-map        (HashMap.)]
;    (prn (keys old-hla-map))
    (.put new-hla-map (util/safe-get noop-schema :name) noop-schema) ; Must put this here, since it has no refs.
    (util/make-safe (put-grounded-hlas root-action-name {} instance old-hla-map new-hla-map))
    (doseq [[k v] (doall (seq new-hla-map))] (when (util/includes? [:on-stack :bad] (first v)) (.remove new-hla-map k)))
    (println "Number of grounded actions: " (count (keys new-hla-map)))
    (make-grounded-strips-hla
     new-hla-map 
     (util/safe-get new-hla-map (list root-action-name))
     envs/*true-condition*)))

(defmethod hla-environment                ::GroundedStripsHLA [hla] (util/safe-get (util/safe-get hla :schema) :env))
(defmethod hla-name                       ::GroundedStripsHLA [hla] (:name (:schema hla)))
(defmethod hla-primitive?                 ::GroundedStripsHLA [hla] (when (:primitive (:schema hla)) true))
(defmethod hla-primitive                  ::GroundedStripsHLA [hla] (:primitive (:schema hla)))
(defmethod hla-hierarchical-preconditions ::GroundedStripsHLA [hla] (:hierarchical-precondition hla))
(defmethod hla-optimistic-description     ::GroundedStripsHLA [hla] (:opt-desc (:schema hla)))
(defmethod hla-pessimistic-description    ::GroundedStripsHLA [hla] (:pess-desc (:schema hla)))

(defmethod hla-immediate-refinements     [::GroundedStripsHLA :edu.berkeley.ai.angelic/PropositionalValuation] 
  [hla opt-val] ((:ref-fn (:schema hla)) hla opt-val)) 

(comment 
  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (ground-and-constant-simplify-strips-hierarchy (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env) dont-constant-simplify-strips-planning-instance))] node) ;(time (second (a-star-search node))))
  )



(comment 


; TODO: may leave bad actions in map... oh well? 
(defn get-grounded-refinement-schema-instantiation [ref-schema var-map instance old-hla-map new-mutable-hla-map]
  (let [[name pos-pre neg-pre unk-types expansion] ref-schema
	{:keys [always-true-atoms always-false-atoms]} instance
	grounder #(props/simplify-atom var-map %)
	vm-translator #(translate-var-map (util/safe-get old-hla-map (first %)) (rest %) var-map)
	new-pos-pre (util/difference (set (map grounder pos-pre)) always-true-atoms)
	new-neg-pre (util/difference (set (map grounder neg-pre)) always-false-atoms)
	precondition (envs/make-conjunctive-condition new-pos-pre new-neg-pre)]
;    (prn name var-map)
    (when (and (empty? (util/intersection new-pos-pre always-false-atoms))
	       (empty? (util/intersection new-neg-pre always-true-atoms)))
      (util/assert-is (not (empty? expansion)) "Test %s" ref-schema)
;      (if (empty? expansion) [precondition []] ; handle first action specially
	(let [ground-first-action-name (grounder (first expansion))]
	  (when (put-grounded-hlas (ffirst expansion) (vm-translator (first expansion)) 
				   instance old-hla-map new-mutable-hla-map)
;	    (prn "First" (first expansion) ground-first-action-name (vm-translator (first expansion)) " of " name var-map)
	    (let [ground-first-action (util/safe-get new-mutable-hla-map ground-first-action-name)
		  precondition (envs/conjoin-conditions precondition (if (= (first ground-first-action) :on-stack)
									    (second ground-first-action)
									  (util/safe-get ground-first-action :precondition)))]				  
	      (loop [ground-expansion [ground-first-action-name], 
		     expansion (rest expansion)]
		(if (empty? expansion) [precondition ground-expansion]
		  (when (put-grounded-hlas (ffirst expansion) (vm-translator (first expansion))
					   instance old-hla-map new-mutable-hla-map)
		    (recur (conj ground-expansion (grounder (first expansion))) (rest expansion)))))))))))

; TODO: For now, do totally braindedad thing
(defn get-possible-ref-schema-var-maps [ref-schema var-map objects always-true-atoms always-false-atoms]
  (let [dummy-vals (seq (get-dummy-var-val-map objects (nth ref-schema 3)))]
;    (prn (count (apply util/my-combinations (map second dummy-vals))))
    (for [combo (apply util/my-combinations (map second dummy-vals))]
      (into var-map (map vector (map first dummy-vals) combo)))))


(defn constant-simplify-strips-action [action true-atoms false-atoms]
  (util/assert-is (nil? (util/safe-get action :vars)))
  (let [pos-pre    (util/difference (util/to-set (util/safe-get action :pos-pre)) true-atoms)
        neg-pre    (util/difference (util/to-set (util/safe-get action :neg-pre)) false-atoms)]
    (when (and (empty? (util/intersection pos-pre false-atoms))
               (empty? (util/intersection neg-pre true-atoms)))
      (strips/make-strips-action-schema 
       (util/safe-get action :name)
       nil
       pos-pre
       neg-pre
       (util/safe-get action :add-list)
       (util/safe-get action :delete-list)
       (util/safe-get action :cost))))) 

; Puts this action and descendents into new-hla-map, returning
; true for success or nil for "bad action" (or no refs.)
; Do braindead way for now, speed up later.
; TODO: should really check cycles better, to get rid of things with only infinite refinements.
; Are we even handling refinement preconditions???
; TODO: special case, top-level should match only against initial state ????
(defn put-grounded-hlas [root-name var-map instance old-hla-map #^HashMap new-mutable-hla-map]
;  (print ".")
;  (prn "Put " root-name var-map)
  (let [schema (util/safe-get old-hla-map root-name)
	full-name (into [(util/safe-get schema :name)]
			(map #(util/safe-get var-map (second %)) (util/safe-get schema :vars)))
	old-val (.get new-mutable-hla-map full-name)]
;    (prn (if (<= (count old-val) 2) old-val "
    (cond (= (first old-val) :bad) false
	  old-val                  true
	  :else 
      (let [{:keys [trans-objects always-true-atoms always-false-atoms]} instance
	    {:keys [vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	    grounder #(props/simplify-atom var-map %)
	    new-pos-pre (util/difference (set (map grounder pos-pre)) always-true-atoms)
	    new-neg-pre (util/difference (set (map grounder neg-pre)) always-false-atoms)
	    new-precondition (envs/make-conjunctive-condition new-pos-pre new-neg-pre)
	    opt-desc    (ground-description optimistic-schema  var-map)
	    pess-desc   (ground-description pessimistic-schema var-map)]
;	(prn "step1 " full-name)
	(.put new-mutable-hla-map full-name [:on-stack new-precondition])
	(if-let [result 
  	 (when (and (empty? (util/intersection new-pos-pre always-false-atoms))
		   (empty? (util/intersection new-neg-pre always-true-atoms)))
;	  (prn "step2" refinement-schemata)
	  (if primitive
	      (do (.put new-mutable-hla-map full-name
			(make-grounded-strips-hla-schema instance
			 full-name new-precondition :primitive #(throw (UnsupportedOperationException.)) 
			 opt-desc pess-desc
			 (strips/strips-action->action
 			    (util/make-safe (constant-simplify-strips-action ; some redundancy here... 
					     (strips/get-strips-action-schema-instance primitive var-map)
					     always-true-atoms always-false-atoms)))))
		  true)
	    (when-let [refs 
		       (doall 
			(filter identity
			      (for [ref-schema refinement-schemata
				    full-var-map (get-possible-ref-schema-var-maps ref-schema 
						   var-map trans-objects always-true-atoms always-false-atoms)]
				(do ;(prn "try " ref-schema full-var-map)
				(get-grounded-refinement-schema-instantiation 
				 ref-schema full-var-map instance old-hla-map new-mutable-hla-map)))))]
;	      (prn "step3")
	      (.put new-mutable-hla-map full-name		    
		    (make-grounded-strips-hla-schema instance
		     full-name new-precondition refs (make-refinement-generator refs) opt-desc pess-desc nil))
	      true)))]
	  result
	 (do (.put new-mutable-hla-map full-name [:bad]) false))))))


     
(defn ground-and-constant-simplify-strips-hierarchy [hla instance-simplifier]
  (util/assert-is (= (:class hla) ::StripsHLA))
  (let [old-hierarchy      (util/safe-get hla :hierarchy)
	root-action-name   (util/safe-get (util/safe-get hla :schema) :name)
	old-hla-map        (util/safe-get old-hierarchy :hla-map)
	instance           (instance-simplifier (util/safe-get old-hierarchy :problem-instance))
	noop-schema        (make-grounded-strips-noop-schema instance)
	new-hla-map        (HashMap.)]
;    (prn (keys old-hla-map))
    (.put new-hla-map (util/safe-get noop-schema :name) noop-schema) ; Must put this here, since it has no refs.
    (util/make-safe (put-grounded-hlas root-action-name {} instance old-hla-map new-hla-map))
    (doseq [[k v] (doall (seq new-hla-map))] (when (util/includes? [:on-stack :bad] (first v)) (.remove new-hla-map k)))
    (println "Number of grounded actions: " (count (keys new-hla-map)))
    (make-grounded-strips-hla
     new-hla-map 
     (util/safe-get new-hla-map (list root-action-name))
     envs/*true-condition*)))
)