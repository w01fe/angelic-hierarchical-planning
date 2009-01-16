(ns edu.berkeley.ai.angelic.hierarchies.strips-hierarchies
  (:refer-clojure)
  (:use [edu.berkeley.ai.angelic :as angelic] 
        [edu.berkeley.ai.angelic.hierarchies :as hierarchies])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
        [edu.berkeley.ai.util.propositions :as props]
        [edu.berkeley.ai.domains.strips :as strips]
        [edu.berkeley.ai.angelic.ncstrips-descriptions :as ncstrips]
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


; TODO: double check about removing precs from NCSTRIPS for primitives.
; TODO: some more general way to do this (without focusing on ncstrips)
(defn- make-strips-primitive-hla-schema [types objects predicates action]
  (let [desc (ncstrips/make-ncstrips-description-schema types (props/check-objects types (concat objects (:vars action))) predicates 
					       [(ncstrips/make-ncstrips-effect (:pos-pre action) (:neg-pre action) (:add-list action) (:delete-list action) nil nil (constantly (:cost action)))] (:vars action))]
    (make-strips-hla-schema (:name action) (:vars action) (:pos-pre action) (:neg-pre action) :primitive desc desc action)))


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
		  [(if ref-name (util/symbol-cat name '- ref-name) (gensym name)) pp np nil expansion])))
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
		(do (util/assert-is (util/includes? var allowed-vars))
		    [var [type]]))))))
   

(defn- check-hla-schema [types guaranteed-objs predicates all-actions hla-schema] 
  (util/assert-is (not (map? (:vars hla-schema))))
  (util/assert-is (apply distinct? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
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
     nil)))

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
  (util/assert-is (isa? (:class domain) :strips/StripsPlanningDomain))
  (util/match [[[:multiple (:hla [unquote-seq hlas])]] contents]
    {:class ::StripsHierarchySchema, :hlas
     (check-hla-schemata (:types domain) (:guaranteed-objs domain) (:predicates domain) (:action-schemata domain)
			 (map #(parse-strips-hla-schema % domain) hlas))}))

(defn make-flat-act-optimistic-description-schema [upper-reward-fn]
  {:class ::FlatActOptimisticDescriptionSchema :upper-reward-fn upper-reward-fn})

(defmethod instantiate-description-schema ::FlatActOptimisticDescriptionSchema [desc instance]
  (make-flat-act-optimistic-description (envs/get-goal instance) (:upper-reward-fn desc)))

(defmethod ground-description :angelic.hierarchies/FlatActOptimisticDescription [desc var-map] desc)

; TODO: use ncstrips for Act description?
; Immediate refinements are [name pos-prec neg-prec unk-types expansion]
; TODO: check it's correct to ignore primitive precs.
(defn make-flat-strips-hierarchy-schema [domain upper-reward-fn]
  (util/assert-is (isa? (:class domain) :strips/StripsPlanningDomain))
  {:class ::StripsHierarchySchema
   :hlas 
     (util/map-map #(vector (:name %) %) 
	(cons
	  (make-strips-hla-schema
	   'act nil nil nil
	   (cons ['empty nil nil nil []]
		 (for [action (:action-schemata domain)]
		   (let [dummy-vars (for [[t v] (:vars action)] [(keyword (str "?" v)) [t]])]
		     [(:name action) nil nil (into {} dummy-vars) [(cons (:name action) (map first dummy-vars)) ['act]]]))) 
	   (make-flat-act-optimistic-description-schema upper-reward-fn)
	   *pessimal-description* nil)
	  (map (partial make-strips-primitive-hla-schema 
                 (:types domain) (:guaranteed-objs domain) (:predicates domain))
	       (:action-schemata domain))))})



(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )


;; Grounded STRIPS HLAs and hierarchies (for now, actual grounding done JIT)

(derive ::StripsHLA :angelic.hierarchies/HLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)


; TODO TODO: should eventually remove all dependence on instance
(defstruct strips-hierarchy :class :hla-map :problem-instance)

(defstruct strips-hla :class :hierarchy :schema :var-map :precondition :primitive)

(defn make-strips-hla [hierarchy schema var-map precondition primitive]
  (if primitive
      (struct strips-hla ::StripsPrimitiveHLA hierarchy schema var-map precondition primitive)
    (struct strips-hla ::StripsHLA hierarchy schema var-map precondition nil)))

(defn- instantiate-strips-hla-schema [hla instance]
  (assoc hla
    :optimistic-schema  (instantiate-description-schema (:optimistic-schema hla) instance)
    :pessimistic-schema (instantiate-description-schema (:pessimistic-schema hla) instance)))

(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) :strips/StripsPlanningInstance))
  (let [hla-map (util/map-map (fn [[name hla]] [name (instantiate-strips-hla-schema hla instance)])
			 (util/safe-get hierarchy :hlas))
	act     (util/safe-get hla-map 'act)
	opt-desc  (instantiate-description-schema (parse-description [:opt] :dummy :dummy) instance)
	pess-desc (instantiate-description-schema (parse-description [:pess] :dummy :dummy) instance)
	dummy-vars (for [[t v] (:vars act)] [(keyword (str "?" v)) [t]])]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy hla-map instance)
     (make-strips-hla-schema (gensym "strips-top-level-action") {} nil nil 
			     [[(gensym "strips-top-level-action-ref") nil nil
			       (util/map-map identity dummy-vars) 
			       (list (cons 'act (map first dummy-vars)))]]
			     opt-desc pess-desc nil)  ; Dummy top-level action
     {}
     (envs/make-conjunctive-condition nil nil)
     false
     )))


(comment 
  (instantiate-hierarchy
   (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		    (make-nav-switch-strips-domain))
   (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))

		    )


;; HLA methods
    

(defmethod hla-name                       ::StripsHLA [hla] 
  (cons (:name (:schema hla))
	(replace (:var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive ::StripsHLA [hla] nil)
(defmethod hla-primitive ::StripsPrimitiveHLA [hla] 
  (strips/strips-action->action (strips/get-strips-action-schema-instance (:primitive hla) (:var-map hla))))

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
  (if (empty? expansion)   ; must handle empty expansion specially
      (do (util/assert-is (empty? dummy-var-vals))
	  (when-not (empty-valuation? (restrict-valuation opt-val precondition))
	    ['()]))
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
		     (repeat (envs/make-conjunctive-condition nil nil)))))))))


(defmethod hla-immediate-refinements [::StripsPrimitiveHLA :angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-immediate-refinements     [::StripsHLA :angelic/PropositionalValuation] [hla opt-val]
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
		 
     

