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
					      (:add-list action) (:delete-list action) nil nil nil nil nil 
					      (if (number? (:cost action)) (constantly (:cost action)) (:cost-fn action)))] 
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
	  (util/partition-all 2 (next hla))]
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
      (let [params (next action)
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
       (map vector (next action) (util/safe-get all-actions (first action)))))))
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

(defmethod parse-description :flat-act [desc domain params]
  (util/assert-is (= (count desc) 2))
  (make-flat-act-optimistic-description-schema (second desc)))

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
	   (parse-description (if (fn? upper-reward-fn) [:flat-act upper-reward-fn] upper-reward-fn) domain nil)
	      ;make-flat-act-optimistic-description-schema upper-reward-fn)
	   *pessimal-description* nil)
	  (map #(make-strips-primitive-hla-schema 
                 (:types domain) (:guaranteed-objs domain) (:predicates domain) %)
	       (:action-schemata domain)))))})

(defn get-flat-strips-hierarchy 
  ([env] (get-flat-strips-hierarchy env (constantly 0)))
  ([env act-desc-or-upper-reward-fn]
   (instantiate-hierarchy 
    (make-flat-strips-hierarchy-schema (envs/get-domain env) act-desc-or-upper-reward-fn) env)))



(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )







;; Grounded STRIPS HLAs and hierarchies (here, actual grounding done JIT, not cached)
; Immediate refinements are [name pos-prec neg-prec CSP (not unk-types) expansion !!!]

(derive ::StripsHLA :angelic.hierarchies/HLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)
(derive ::StripsNoopHLA ::StripsPrimitiveHLA)

; keep around old map for ahlrta*
(defstruct strips-hierarchy :class :hla-map :problem-instance :hla-schema-map)

(defstruct strips-hla :class :hierarchy :schema :var-map :precondition)

(defn make-strips-hla [hierarchy schema var-map precondition primitive]
  (struct strips-hla 
	  (cond (= primitive :noop) ::StripsNoopHLA primitive ::StripsPrimitiveHLA :else ::StripsHLA)
	  hierarchy schema var-map precondition))


(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map]
  (let [hla-vars (:vars hla)]
    (loop [ret {}, args (seq args), vars (seq (:vars hla))]
      (util/assert-is (not (util/xor args vars)))
      (if (not args) ret
	(recur (assoc ret (second (first vars)) (util/safe-get var-map (first args)))
	       (next args) (next vars))))))

;; pulls all ***constant*** constraints from refinement, not just first action? 
(defn- extract-preconditions [var-map action-inst hla-map] "Returns [pos neg]"
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

(defn- get-dummy-var-val-map [objects dummy-var-type-map]
  (util/map-vals (fn [t] (util/safe-get objects t)) dummy-var-type-map))

; CSP takes on sole responsibility for handling *all* constant predicates.  Really (?)
; TODO: drop all constants here!  BUT must do it in right order?
(defn instantiate-strips-hla-schema [schema instance hla-map trans-objects const-pred-map]
  (let [{:keys [name vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	const-preds  (util/keyset const-pred-map)
	deconst      (fn [atoms] (remove #(const-preds (first %)) atoms))]
 ;   (println name refinement-schemata)
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
			      (next expansion)))))]
	   (util/assert-is (not (empty? expansion)))
;	   (print "\nConstructing  ref CSP for " name " " r-name ": " );(set all-pos-pre) (set all-neg-pre)) 
	   [r-name (deconst pos-prec) (deconst neg-prec) 
	    (smart-csps/create-smart-csp (set all-pos-pre) (set all-neg-pre) arg-val-map dummy-val-map const-pred-map instance)
	    expansion]))))
     (instantiate-description-schema optimistic-schema instance)
     (instantiate-description-schema pessimistic-schema instance)
     (if (or (not primitive) (= primitive :noop)) primitive  ; TODO: hacky.
	 (constant-simplify-strips-primitive-schema primitive const-preds)))))



(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (let [old-hla-map    (util/safe-get hierarchy :hlas)
	act-vars       (util/safe-get-in old-hla-map ['act :vars])
	root-hla-name  (gensym "strips-top-level-action")
	old-hla-map    (assoc old-hla-map root-hla-name
			 (make-strips-hla-schema root-hla-name [] nil nil 
			   [["act" nil nil (util/map-map (fn [[t v]] [v t]) act-vars) 
			     [(into '[act] (map second act-vars))]]]
			   (parse-description [:opt] :dummy :dummy)
			   (parse-description [:pess] :dummy :dummy)
			   nil))
	trans-objects  (util/safe-get instance :trans-objects)
	const-pred-map (:const-pred-map instance)
	new-hla-map    (util/map-vals 
			#(instantiate-strips-hla-schema % instance old-hla-map trans-objects const-pred-map)
			old-hla-map)]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy new-hla-map instance old-hla-map)
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
    
(defmethod hla-default-valuation-type ::StripsHLA [hla] 
  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation)

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
			   trans-var-map (translate-var-map hla (next call) final-var-map)
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



;; Used by AHLRTA

(defn convert-to-prim-act-strips-hla [initial-node]
  (let [{:keys [hierarchy schema var-map precondition]} initial-node,
	{:keys [hla-schema-map problem-instance]}              hierarchy,
	{:keys [trans-objects const-pred-map domain]}          problem-instance,
	act-vars      (map (fn [[t v]] [v t]) (util/safe-get-in hla-schema-map ['act :vars]))
	prim-action-schemata (util/safe-get domain :action-schemata)]
    (make-strips-hla
     hierarchy
     (instantiate-strips-hla-schema
      (make-strips-hla-schema 
       (gensym "pa-strips-top-level-action")
       [] nil nil
       (for [action prim-action-schemata]
	 (let [prim-vars (for [[t v] (:vars action)] [(gensym (str "?" v)) t])]
	   [(:name action) nil nil (into {} (concat prim-vars act-vars)) 
	    [(into [(:name action)] (map first prim-vars)) 
	     (into ['act] (map first act-vars))]]))
       (parse-description [:opt] :dummy :dummy)
       (parse-description [:pess] :dummy :dummy)
       nil)
      problem-instance hla-schema-map trans-objects const-pred-map)
     {}
     envs/*true-condition*
     false)))

;; Used in decomposition
; TODO: DANGEROUS
(defn sub-environment-hla "Change the initial state and goal associated iwth this hierarchy.  This may be very dangerous since things like goal- predicates and descriptions will not be re-instantiated.  Can only be used safely when all references to the goal are in actions with pessimal pessimisitc descriptions, and actions with non-vacuous pessimistic descriptions never refine to such actions."
  [hla new-init new-goal]
  (assoc hla
    :hierarchy 
    (assoc (util/safe-get hla :hierarchy)
      :problem-instance
      (envs/sub-environment (util/safe-get-in hla [:hierarchy :problem-instance]) new-init new-goal))))




(comment 
  (let [domain (make-nav-switch-strips-domain), env (constant-predicate-simplify (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env))] (count node))


  (let [domain (make-nav-switch-strips-domain), env (constant-predicate-simplify (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env))] (count node))


 ;(time (second (a-star-search node))))
  )
	      







