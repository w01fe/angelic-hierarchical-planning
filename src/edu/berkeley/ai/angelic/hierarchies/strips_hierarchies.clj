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

;; dummy variables
; Right now, only allow :?s to be introduced by the *first* HLA of an expansion
; Eventually, relax this by an automatic translation?  

; Immediate refinements are [name pos-prec neg-prec unk-types expansion]

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
	      [(ncstrips/make-ncstrips-effect nil nil ; (:pos-pre action) (:neg-pre action) TODO: double check
					      (:add-list action) (:delete-list action) nil nil (constantly (:cost action)))] 
	      (:vars action))]
    (make-strips-hla-schema (:name action) (:vars action) (:pos-pre action) (:neg-pre action) 
			    :primitive desc desc action)))


(defn parse-strips-hla-schema [hla domain]
  (util/match [#{[:optional [:parameters   [unquote parameters]]]
	    [:optional [:precondition [unquote precondition]]]
	    [:multiple [:refinement   [unquote refinements]]]
	    [:optional [:optimistic   [unquote optimistic]]]
	    [:optional [:pessimistic  [unquote pessimistic]]]
	    [:optional [:exact        [unquote exact]]]}
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
	      (util/match [[[:optional [:name [unquote ref-name]]]
			    [:optional [:precondition [unquote precondition]]]
			    [:expansion [unquote expansion]]]
			   (util/partition-all 2 refinement)]
		(let [[pp np] (props/parse-pddl-conjunction precondition)] 
		  [(if ref-name (util/symbol-cat name '- ref-name) (gensym name)) pp np nil (or (seq expansion) (list (list (:name *noop-strips-hla-schema*))))])))
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
      (seq action)))))

(defn get-dummy-var-type-map [types all-actions expansion]
  (let [allowed-vars (filter props/is-dummy-var? (rest (first expansion)))]
    (util/map-map (fn [[var ts]] [var (props/maximal-subtypes types ts)])
	     (util/merge-reduce concat {} 
	      (for [action expansion
		    [var type] (map vector (rest action) (util/safe-get all-actions (first action)))
		    :when (props/is-dummy-var? var)]
		(do (util/assert-is (util/includes? allowed-vars var))
		    [var [type]]))))))
   

(defn- check-hla-schema [types guaranteed-objs predicates all-actions hla-schema] 
  (util/assert-is (contains? #{nil :noop} (util/safe-get hla-schema :primitive)))
  (util/assert-is (not (map? (:vars hla-schema))))
  (util/assert-is (util/distinct-elts? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
  (util/assert-is (not-any? #(props/is-dummy-var? (second %)) (:vars hla-schema))) 
  (let [vars-and-objects (props/check-objects types (concat guaranteed-objs (:vars hla-schema)))
	atom-checker     (fn [atoms] (map #(props/check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-hla-schema 
     (:name hla-schema)
     (:vars hla-schema)
     (atom-checker (:pos-pre hla-schema))
     (atom-checker (:neg-pre hla-schema))
     (doall 
     (map (fn [[name pos-pre neg-pre dummy-map expansion]]
	    (util/assert-is (empty? dummy-map))
	    (let [dummy-map (get-dummy-var-type-map types all-actions expansion)
		  impl-vars-and-objects (util/merge-reduce concat  vars-and-objects   ; add dummy vars
						   (for [[v ts] dummy-map
							 t ts]
						     [t [v]]))
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
    (let [hla-schemata (doall (map (partial check-hla-schema types guaranteed-objs predicates all-actions) hla-schemata))]
      (util/assert-is (some #(= (:name %) 'act) hla-schemata))
      (util/map-map #(vector (:name %) %) 
	       (concat hla-schemata
		       (map (partial make-strips-primitive-hla-schema types guaranteed-objs predicates) actions))))))



;; Parse and check an entire hierarchy   
     
(defmethod parse-hierarchy-type :strips-hierarchy [type contents domain]
  (util/assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (util/match [[[:multiple (:hla [unquote-seq hlas])]] contents]
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
		   (let [dummy-vars (for [[t v] (:vars action)] [(keyword (str "?" v)) [t]])]
		     [(:name action) nil nil (into {} dummy-vars) [(cons (:name action) (map first dummy-vars)) ['act]]]))) 
	   (make-flat-act-optimistic-description-schema upper-reward-fn)
	   *pessimal-description* nil)
	  (map (partial make-strips-primitive-hla-schema 
                 (:types domain) (:guaranteed-objs domain) (:predicates domain))
	       (:action-schemata domain)))))})



(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )





;; Grounded STRIPS HLAs and hierarchies (here, actual grounding done JIT)

(derive ::StripsHLA :angelic.hierarchies/HLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)
(derive ::StripsNoopHLA ::StripsPrimitiveHLA)


; TODO TODO: should eventually remove all dependence on instance
(defstruct strips-hierarchy :class :hla-map :problem-instance)

(defstruct strips-hla :class :hierarchy :schema :var-map :precondition :primitive)

(defn make-strips-hla [hierarchy schema var-map precondition primitive]
  (struct strips-hla 
	  (cond (= primitive :noop) ::StripsNoopHLA primitive ::StripsPrimitiveHLA :else ::StripsHLA)
	  hierarchy schema var-map precondition primitive))

(defn- instantiate-strips-hla-schema [hla instance]
  (assoc hla
    :optimistic-schema  (instantiate-description-schema (:optimistic-schema hla) instance)
    :pessimistic-schema (instantiate-description-schema (:pessimistic-schema hla) instance)))

(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (let [hla-map (util/map-map (fn [[name hla]] [name (instantiate-strips-hla-schema hla instance)])
			 (util/safe-get hierarchy :hlas))
	act     (util/safe-get hla-map 'act)
	opt-desc  (instantiate-description-schema (parse-description [:opt] :dummy :dummy) instance)
	pess-desc (instantiate-description-schema (parse-description [:pess] :dummy :dummy) instance)
	dummy-vars (for [[t v] (:vars act)] [(keyword (str "?" v)) [t]])
	top-level-schema 
	  (make-strips-hla-schema (gensym "strips-top-level-action") {} nil nil 
			     [[(gensym "strips-top-level-action-ref") nil nil
			       (util/map-map identity dummy-vars) 
			       (list (cons 'act (map first dummy-vars)))]]
			     opt-desc pess-desc nil)
	final-hla-map (assoc hla-map (util/safe-get top-level-schema :name) top-level-schema)]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy final-hla-map instance)
     top-level-schema
     {}
     envs/*true-condition*
     false
     )))


(comment 
  (instantiate-hierarchy
   (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		    (make-nav-switch-strips-domain))
   (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))

		    )


;; HLA methods
    
(defmethod hla-environment ::StripsHLA [hla] (util/safe-get (util/safe-get hla :hierarchy) :problem-instance))

(defmethod hla-name                       ::StripsHLA [hla] 
  (cons (:name (:schema hla))
	(replace (:var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive? ::StripsHLA [hla] false)
(defmethod hla-primitive ::StripsHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-primitive? ::StripsPrimitiveHLA [hla] true) 
(defmethod hla-primitive ::StripsPrimitiveHLA [hla] 
  (strips/strips-action->action (strips/get-strips-action-schema-instance (:primitive hla) (:var-map hla))))

(defmethod hla-primitive? ::StripsNoopHLA [hla] true) 
(defmethod hla-primitive ::StripsNoopHLA [hla] :noop) 


(defmethod hla-hierarchical-preconditions ::StripsHLA [hla]
  (:precondition hla))

(defmethod hla-optimistic-description     ::StripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (:var-map hla)))
  
(defmethod hla-pessimistic-description    ::StripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (:var-map hla)))

(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map pass-dummy?]
;  (prn (:vars hla) args var-map pass-dummy?)
  (let [hla-vars (:vars hla)]
    (util/assert-is (= (count args) (count hla-vars)) "%s %s %s %s" (:name hla) (:vars hla) args var-map)
    (util/map-map (fn [[arg hla-var]] [hla-var (if (and pass-dummy? (props/is-dummy-var? arg))
					      arg
					    (util/safe-get var-map arg))]) 
	     (map #(vector %1 (second %2)) args hla-vars))))


(defn- refinement-instantiations [precondition hierarchy expansion opt-val var-map dummy-var-vals]
  (util/assert-is (not (empty? expansion)))
    (let [hla-map      (util/safe-get hierarchy :hla-map),
	  first-action (util/safe-get hla-map (ffirst expansion)),
	  first-var-map (translate-var-map first-action (rfirst expansion) var-map true)
	  quasi-ground-first-precondition (envs/conjoin-conditions
					   (envs/make-conjunctive-condition
					    (map (partial props/simplify-atom first-var-map) (:pos-pre first-action))
					    (map (partial props/simplify-atom first-var-map) (:neg-pre first-action)))
					   precondition)]
      (for [dummy-var-map (valuation-consistent-mappings opt-val quasi-ground-first-precondition dummy-var-vals)]
	(let [final-var-map (merge var-map dummy-var-map)]
	  (map (fn [call extra-preconditions]
		 (let [hla (util/safe-get hla-map (first call))
		       trans-var-map (translate-var-map hla (rest call) final-var-map false)]
;		   (prn (rest call) final-var-map trans-var-map)
		   (make-strips-hla 
		    hierarchy 
		    hla 
		    trans-var-map 
		    (envs/conjoin-conditions 
		     (envs/make-conjunctive-condition
		      (map (partial props/simplify-atom trans-var-map) (util/safe-get hla :pos-pre)) 
		      (map (partial props/simplify-atom trans-var-map) (util/safe-get hla :neg-pre))) 
		     extra-preconditions)
		    (:primitive hla))))
	       expansion 
	       (cons (envs/ground-propositional-condition  precondition dummy-var-map)
		     (repeat envs/*true-condition*)))))))


(defmethod hla-immediate-refinements [::StripsPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-immediate-refinements     [::StripsHLA :edu.berkeley.ai.angelic/PropositionalValuation] [hla opt-val]
  (let [opt-val (restrict-valuation opt-val (:precondition hla))
	hierarchy (:hierarchy hla)
	objects   (:trans-objects (:problem-instance hierarchy))
	var-map   (:var-map hla)]
    (when-not (empty-valuation? opt-val)
      (util/forcat [[name pos-pre neg-pre dummy-type-map expansion] (:refinement-schemata (:schema hla))]
	 (let [quasi-ground-impl-pre (envs/make-conjunctive-condition
				      (map (partial props/simplify-atom var-map) pos-pre)
				      (map (partial props/simplify-atom var-map) neg-pre))
	       dummy-val-map (util/map-map (fn [[var types]] [var (util/forcat [t types] (util/safe-get objects t))]) 
				      dummy-type-map)]
	   (refinement-instantiations (envs/conjoin-conditions quasi-ground-impl-pre (:precondition hla))
				      hierarchy
				      expansion
				      opt-val
				      var-map
				      dummy-val-map))))))














;;;;;;;;; Ungrounded but constant-simplified strips-hierarchies.

(derive ::StripsCSHLA          ::StripsHLA)

; Immediate refinements are [name pos-prec neg-prec CSP (not unk-types) expansion !!!]
;(defstruct strips-hla-schema :class :name :vars :pos-pre :neg-pre :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)

; TODO: tricky part here will be to handle constants & properly prepare CSPs -- move stuff from immediate-refs to instantiation time.

(defstruct strips-cs-hierarchy :class :hla-map :problem-instance :always-true :always-false)

(defstruct strips-cs-hla :class :hierarchy :schema :var-map :precondition :primitive)

(defn make-strips-cs-hla [hierarchy schema var-map precondition primitive]
  (struct strips-cs-hla (cond (= primitive :noop) ::StripsNoopHLA primitive ::StripsPrimitiveHLA :else ::StripsCSHLA)
	  hierarchy schema var-map precondition primitive))

;; pulls all ***constant*** constraints from refinement, not just first action?  Meh, you can restate it if you want.
;; this way we don't need to filter in hla-immediate-refinements
 ; (assuming no inertia, only constant.)

; TODO: pull *all* hierarchical constraints i.e., when unary refinements?  NO.

(defn extract-preconditions [var-map action-inst hla-map] "Returns [pos neg]"
  (let [[act-name & args] action-inst
	hla (util/safe-get hla-map act-name)
	trans-var-map (translate-var-map hla args var-map false)]
    ;(println act-name (:pos-pre hla) (:neg-pre hla))
    [(map (partial props/simplify-atom trans-var-map) (:pos-pre hla))
     (map (partial props/simplify-atom trans-var-map) (:neg-pre hla))]))
	
;(def *csps* nil)  
; CSP takes on sole responsibility for handling constant predicates.
(defn add-schema-ref-csps [schema hla-map trans-objects const-pred-map]
  (let [{:keys [name vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	const-preds  (util/keyset const-pred-map)]
;    (println name refinement-schemata vars)
    (make-strips-hla-schema 
     name vars pos-pre neg-pre
     (if (coll? refinement-schemata) 
       (doall
     (for [[r-name pos-prec neg-prec dummy-type-map expansion] refinement-schemata]   
	 (let [arg-val-map   (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
	       dummy-val-map (util/map-map (fn [[var types]] [var (util/forcat [t types] (util/safe-get trans-objects t))]) 
					   dummy-type-map)
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
	   (print "Constructing CSP for " name " " r-name ": " );(set all-pos-pre) (set all-neg-pre)) 
;	   (def *csps* (cons [(str name ":" r-name) (smart-csps/create-smart-csp (set all-pos-pre) (set all-neg-pre) arg-val-map dummy-val-map const-pred-map)] *csps*))
	   [r-name pos-prec neg-prec 
	    (smart-csps/create-smart-csp (set all-pos-pre) (set all-neg-pre) arg-val-map dummy-val-map const-pred-map)
	    expansion])))
     refinement-schemata)
     optimistic-schema pessimistic-schema 
     (if (or (not primitive) (= primitive :noop)) primitive  ; TODO: hacky.
       (strips/make-strips-action-schema 
	(:name primitive)
	(:vars primitive)
	(remove #(const-preds (first %)) (:pos-pre primitive))
	(remove #(const-preds (first %)) (:neg-pre primitive))
	(remove #(const-preds (first %)) (:add-list primitive))
	(remove #(const-preds (first %)) (:delete-list primitive))
	(:cost primitive))))))

    



(defn constant-simplify-strips-hierarchy [hla instance-simplifier]
  (util/assert-is (= (:class hla) ::StripsHLA))
  (let [old-hierarchy      (util/safe-get hla :hierarchy)
	root-hla-name      (util/safe-get (util/safe-get hla :schema) :name) 
	root-hla-precond   (util/safe-get hla :precondition)
	root-hla-primitive (util/safe-get hla :primitive)
	old-hla-map        (util/safe-get old-hierarchy :hla-map)
	instance           (instance-simplifier (util/safe-get old-hierarchy :problem-instance))
	always-true        (util/safe-get instance :always-true-atoms)
	always-false       (util/safe-get instance :always-false-atoms)
	const-preds        (get (util/safe-get instance :domain) :const-predicates)
	const-pred-map     (reduce (fn [m [pred & args]] (util/assoc-cons m pred args)) {} always-true)
	new-hla-map        (util/map-vals #(add-schema-ref-csps % old-hla-map (util/safe-get instance :trans-objects) const-pred-map) 
					  old-hla-map)]
    (util/assert-is (= envs/*true-condition* root-hla-precond))
    (util/assert-is (not root-hla-primitive))
    (doseq [pred (concat always-true always-false)] (util/assert-is (const-preds (first pred))))  ; Only const preds, no inertia
    (make-strips-cs-hla
     (struct strips-cs-hierarchy ::StripsCSHierarchy new-hla-map instance always-true always-false)
     (util/safe-get new-hla-map root-hla-name)
     (util/safe-get hla :var-map)
     root-hla-precond
     root-hla-primitive)))


;; HLA methods mostly inherited from above


(defmethod hla-immediate-refinements     [::StripsCSHLA :edu.berkeley.ai.angelic/PropositionalValuation] [hla opt-val]
  (let [opt-val      (restrict-valuation opt-val (:precondition hla))
	var-map      (:var-map hla)	
	hierarchy    (:hierarchy hla)
	precondition (:precondition hla)
	always-true  (:always-true hierarchy)
	always-false (:always-false hierarchy)
	hla-map      (:hla-map hierarchy)]
    (when-not (empty-valuation? opt-val)
      (let [val-pred-maps (valuation->pred-maps opt-val)]
;	  (println val-pred-maps (map first (:refinement-schemata (:schema hla))))
  	  (for [[name pos-pre neg-pre csp expansion] (:refinement-schemata (:schema hla))
	        dummy-var-map (smart-csps/get-smart-csp-solutions csp var-map val-pred-maps)]
	    (let [final-var-map (merge var-map dummy-var-map)
		  simplifier (partial props/simplify-atom final-var-map)
		  ground-impl-pre (envs/make-conjunctive-condition
				   (map simplifier pos-pre)
				   (map simplifier neg-pre))]
;	      (println val-pred-maps ground-impl-pre)
;	      (println "fv " name dummy-var-map)
	      (map (fn [call extra-preconditions]
		     (let [hla (util/safe-get hla-map (first call))
			   trans-var-map (translate-var-map hla (rest call) final-var-map false)
 	   		   simplifier (partial props/simplify-atom trans-var-map)
			   precond 
			   (envs/constant-simplify-condition
			    (envs/conjoin-conditions 
			     (envs/make-conjunctive-condition
			      (map simplifier (util/safe-get hla :pos-pre)) 
			      (map simplifier (util/safe-get hla :neg-pre))) 
			     extra-preconditions)
			    always-true always-false)]
;		       (println "tv " trans-var-map)
;		       (when-not (= precond envs/*false-condition*)
		       (make-strips-cs-hla hierarchy hla trans-var-map precond (:primitive hla)))) 
		   expansion
		   (cons (envs/conjoin-conditions precondition ground-impl-pre)
			 (repeat envs/*true-condition*)))))))))

(comment 
  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (constant-simplify-strips-hierarchy (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env) constant-predicate-simplify-strips-planning-instance))] (count node))


  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (constant-simplify-strips-hierarchy (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env) constant-predicate-simplify-strips-planning-instance))] (count node))


 ;(time (second (a-star-search node))))
  )
	      

















;;; Fully grounded and constant-simplified strips hierarchies 	
; For now, generate refinements by filtering, later add refinement generator. 	 

; can't fully fully bottom out because of hierarchical preconditions!?!??!?
; ref-fn should automagically handle hierarchical preconds . . . takes grounded-hla and valuation as args.
; Immediate refinements are [name pos-prec neg-prec unk-types expansion]

; refs in :refs are [name precondition expansion-names]
; ref-fn must process these.

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

; TODO: (maybe): ground out high-level preconditions too???
; input refs are [precondition expansion-names]
; output refs, seqs of grounded-strips-hal,  (given grounded-strips-hla and optimistic-valuations)
; Keep in mind, high-level precondition of first action already taken into account!
  ; TODO: no-op for empty refinement!
 ; For now, do simplest stupid thing. TODO: improve!
; TODO TODO TODO: make lazy again; this is just for profiling

(comment ;old version
(defn make-refinement-generator [refs]
  (fn generate-refinements [hla opt-val]
    (doall 
    (let [{:keys [hla-map hierarchical-precondition]} hla]
      (for [[prec exp] refs :when (not (empty-valuation? (restrict-valuation opt-val prec)))]
	;; TODO: empty ref here!
	(when (seq exp)
	  (cons (let [first-schema (util/safe-get hla-map (first exp))]
		  (make-grounded-strips-hla 
		   hla-map first-schema  
		   (envs/conjoin-conditions hierarchical-precondition (util/safe-get first-schema :precondition))))
	    (for [act (rest exp)]
	      (let [schema (util/safe-get hla-map act)]
		(make-grounded-strips-hla hla-map schema (util/safe-get schema :precondition)))))))))))
 )

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


(import '(java.util HashMap))

(declare put-grounded-hlas)
; Return [precondition expansion-names], or nil for fail. Maybe: save name?
; TODO: may leave bad actions in map... oh well? 

;(def *x* (util/sref 0))
(defn get-grounded-refinement-schema-instantiation [ref-schema var-map instance old-hla-map new-mutable-hla-map]
;  (pr)
;  (util/sref-up! *x* inc)
  (let [[name pos-pre neg-pre unk-types expansion] ref-schema
	{:keys [always-true-atoms always-false-atoms]} instance
	grounder (partial props/simplify-atom var-map)
	vm-translator #(translate-var-map (util/safe-get old-hla-map (first %)) (rest %) var-map false)
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
  (let [unk-types (nth ref-schema 3)
	dummy-vals (seq (util/map-map (fn [[var types]] [var (util/forcat [t types] (util/safe-get objects t))]) 
				      unk-types))]
;    (prn (count (apply util/my-combinations (map second dummy-vals))))
    (for [combo (apply util/my-combinations (map second dummy-vals))]
      (into var-map (map vector (map first dummy-vals) combo)))))

; Puts this action and descendents into new-hla-map, returning
; true for success or nil for "bad action" (or no refs.)
; Do braindead way for now, speed up later.
; TODO: should really check cycles better, to get rid of things with only infinite refinements.
; TODO: special case, top-level should match only against initial state ????
(defn put-grounded-hlas [root-name var-map instance old-hla-map new-mutable-hla-map]
;  (print ".")
;  (prn "Put " root-name var-map)
  (let [schema (util/safe-get old-hla-map root-name)
	full-name (cons (util/safe-get schema :name)
			(map #(util/safe-get var-map (second %)) (util/safe-get schema :vars)))
	old-val (.get new-mutable-hla-map full-name)]
;    (prn (if (<= (count old-val) 2) old-val "
    (cond (= (first old-val) :bad) false
	  old-val                  true
	  :else 
      (let [{:keys [trans-objects always-true-atoms always-false-atoms]} instance
	    {:keys [vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	    grounder (partial props/simplify-atom var-map)
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
 			    (util/make-safe (strips/constant-simplify-strips-action ; some redundancy here... 
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

(defmethod hla-environment                ::GroundedStripsHLA [hla] (util/safe-get (util/safe-get hla :schema) :env))
(defmethod hla-name                       ::GroundedStripsHLA [hla] (:name (:schema hla)))
(defmethod hla-primitive?                  ::GroundedStripsHLA [hla] (when (:primitive (:schema hla)) true))
(defmethod hla-primitive                  ::GroundedStripsHLA [hla] (:primitive (:schema hla)))
(defmethod hla-hierarchical-preconditions ::GroundedStripsHLA [hla] (:hierarchical-precondition hla))
(defmethod hla-optimistic-description     ::GroundedStripsHLA [hla] (:opt-desc (:schema hla)))
(defmethod hla-pessimistic-description    ::GroundedStripsHLA [hla] (:pess-desc (:schema hla)))

(defmethod hla-immediate-refinements     [::GroundedStripsHLA :edu.berkeley.ai.angelic/PropositionalValuation] 
  [hla opt-val] ((:ref-fn (:schema hla)) hla opt-val)) 

(comment 
  (let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (ground-and-constant-simplify-strips-hierarchy (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env) dont-constant-simplify-strips-planning-instance))] node) ;(time (second (a-star-search node))))
  )