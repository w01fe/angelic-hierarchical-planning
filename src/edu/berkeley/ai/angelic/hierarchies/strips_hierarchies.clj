(ns edu.berkeley.ai.angelic.hierarchies.strips-hierarchies
  (:refer-clojure)
  (:use clojure.contrib.seq-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.envs edu.berkeley.ai.util.propositions edu.berkeley.ai.domains.strips edu.berkeley.ai.angelic edu.berkeley.ai.angelic.dnf-simple-valuations edu.berkeley.ai.angelic.ncstrips-descriptions edu.berkeley.ai.angelic.hierarchies)
  )

; Right now, only allow :?s to be introduced by the *first* HLA of an expansion
; Eventually, relax this by an automatic translation?  
; TODO: add optional refinement names.


; Immediate refinements are [name pos-prec neg-prec unk-types expansion]

; TODO: handle :?
; TODO: right now, :? does not quite play properly with subtypes (should find least subtype and store somewhere). 
; TODO: To handle :? correctly, must be able to create new union subtypes.  For now, will just fail fast. 

(defstruct strips-hla-schema :class :name :vars :pos-pre :neg-pre :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)

(defn make-strips-hla-schema [name parameters pos-preconditions neg-preconditions refinement-schemata optimistic-schema pessimistic-schema primitive]
  (struct strips-hla-schema ::StripsHLASchema name parameters pos-preconditions neg-preconditions 
	  refinement-schemata optimistic-schema pessimistic-schema primitive))

(defn- check-hla-expansion [types vars-and-objects all-actions expansion]
  (for [action expansion]
    (do 
      (let [params (rest action)
	    declared-types (safe-get all-actions (first action))]
	(assert-is (= (count params) (count declared-types)))
	(doseq [[type par] (map vector declared-types params)]
	  (check-type types vars-and-objects par type)))      
      (seq action))))

;(loop [typed-params (map-vector declared-types params)
;	     vars-and-objects vars-and-objects]
;	(let [[type par] (first typed-params)
;	      vars-and-objects (if (is-dummy-var? par)
;				   (assoc-cat vars-and-objects type [par])
;				 vars-and-objects)]
;	  (check-type types vars-and-objects par type)
;	  (recur (rest typed-params) vars-and-objects)))

;      (cons (first action)
;	    (for [[par type] (map vector params declared-types)]
;	      (do (or (= par :?) (check-type types vars-and-objects par type))
;		  par))))))



(defn get-dummy-var-type-map [types all-actions expansion]
  (let [allowed-vars (filter is-dummy-var? (rest (first expansion)))]
    (map-map (fn [[var ts]] [var (maximal-subtypes types ts)])
	     (map-map-cat identity
	      (for [action expansion
		    [var type] (map vector (rest action) (safe-get all-actions (first action)))
		    :when (is-dummy-var? var)]
		(do (assert-is (includes? var allowed-vars))
		    [var [type]]))))))
   

(defn- check-hla-schema [types guaranteed-objs predicates all-actions hla-schema] 
;  (.println System/out action-schema)
  (assert-is (not (map? (:vars hla-schema))))
;  (prn hla-schema)
  (assert-is (distinct-elts? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
  (assert-is (not-any? #(is-dummy-var? (second %)) (:vars hla-schema))) 
  (let [vars-and-objects (check-objects types (concat guaranteed-objs (:vars hla-schema)))
	atom-checker     (fn [atoms] (map #(check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-hla-schema 
     (:name hla-schema)
     (:vars hla-schema)
     (atom-checker (:pos-pre hla-schema))
     (atom-checker (:neg-pre hla-schema))
     (map (fn [[name pos-pre neg-pre dummy-map expansion]]
	    (assert-is (empty? dummy-map))
	    (let [dummy-map (get-dummy-var-type-map types all-actions expansion)
		  impl-vars-and-objects (merge-cat vars-and-objects   ; add dummy vars
						   (for [[v ts] dummy-map
							 t ts]
						     [t [v]]))
		  impl-atom-checker (fn [atoms] (map #(check-atom types impl-vars-and-objects predicates %) atoms))]
	      (prn (:name hla-schema) dummy-map)
	      [name
	       (impl-atom-checker pos-pre)
	       (impl-atom-checker neg-pre)
	       dummy-map
	       (check-hla-expansion 
		types 
		impl-vars-and-objects
		all-actions 
		expansion)]))
	  (:refinement-schemata hla-schema))
     (:optimistic-schema hla-schema)
     (:pessimistic-schema hla-schema)
     nil)))

; TODO: double check about removing precs from NCSTRIPS for primitives.
(defn- make-strips-primitive-hla-schema [types objects predicates action]
  (let [desc (make-ncstrips-description-schema types (check-objects types (concat objects (:vars action))) predicates 
					       [(make-ncstrips-effect (:pos-pre action) (:neg-pre action) (:adds action) (:deletes action) nil nil (:cost action))])]
    (make-strips-hla-schema (:name action) (:parameters action) (:pos-pre action) (:neg-pre action) :primitive desc desc action)))



(defn- check-hla-schemata [types guaranteed-objs predicates actions hla-schemata]
;  (prn hla-schemata)
  (let [all-actions (merge (map-map #(vector (:name %) (map first (:vars %))) actions)
			   (map-map #(vector (:name %) (map first (:vars %))) hla-schemata))]
;    (prn all-actions)
    (assert-is (= (count all-actions) (+ (count actions) (count hla-schemata))))
    (let [hla-schemata (map (partial check-hla-schema types guaranteed-objs predicates all-actions) hla-schemata)]
      (assert-is (some #(= (:name %) 'act) hla-schemata))
      (map-map #(vector (:name %) %) 
	       (concat hla-schemata
		       (map (partial make-strips-primitive-hla-schema types guaranteed-objs predicates) actions))))))



(defn parse-strips-hla-schema [hla domain]
  (match [#{[:optional [:parameters   [unquote parameters]]]
	    [:optional [:precondition [unquote precondition]]]
	    [:multiple [:refinement   [unquote refinements]]]
	    [:optional [:optimistic   [unquote optimistic]]]
	    [:optional [:pessimistic  [unquote pessimistic]]]
	    [:optional [:exact        [unquote exact]]]}
	  (chunk 2 (rest hla))]
    (when exact (assert-is (nil? optimistic)) (assert-is (nil? pessimistic)))
    (let [name (first hla)
	  [pos-pre neg-pre] (parse-pddl-conjunction precondition)
	   params        (parse-typed-pddl-list parameters)] 
      (make-strips-hla-schema
       name
       params
       pos-pre
       neg-pre
       (map (fn [refinement]
	      (match [[[:optional [:name [unquote ref-name]]]
		       [:optional [:precondition [unquote precondition]]]
		       [:expansion [unquote expansion]]]
		      (chunk 2 refinement)]
		(let [[pp np] (parse-pddl-conjunction precondition)] 
		  [(if ref-name (symbol-cat name '- ref-name) (gensym name)) pp np nil expansion])))
	    refinements)
       (parse-description (or optimistic exact) domain params)
       (parse-description (or pessimistic exact) domain params)
       nil))))
     


;   (assert-is (isa? (:class env) ::StripsPlanningDomain))
;  (let [types      (:types domain) 
;	objects    (:guaranteed-objs domain)
;	predicates (:predicates domain)
;	actions    (:action-schemata domain)]
	     

(defmethod parse-hierarchy-type :strips-hierarchy [type contents domain]
  (assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (match [[[:multiple (:hla [unquote-seq hlas])]] contents]
    {:class ::StripsHierarchySchema, :hlas
     (check-hla-schemata (:types domain) (:guaranteed-objs domain) (:predicates domain) (:action-schemata domain)
			 (map #(parse-strips-hla-schema % domain) hlas))}))
      

(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )



(derive ::StripsHLA :edu.berkeley.ai.angelic.hierarchies/HLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)
(derive ::StripsPrimitiveHLA :edu.berkeley.ai.angelic.hierarchies/PrimitiveHLA)

; TODO TODO: should eventually remove all dependence on instance
(defstruct strips-hierarchy :class :hla-map :problem-instance)

(defstruct strips-hla :class :hierarchy :schema :var-map :precondition :primitive)

(defn make-strips-hla [hierarchy schema var-map precondition primitive]
  (if primitive
      (struct strips-hla ::StripsPrimitiveHLA hierarchy schema var-map precondition primitive)
    (struct strips-hla ::StripsHLA hierarchy schema var-map precondition nil)))


(defn- instantiate-strips-hla-schema [hla instance]
  (assoc hla
    :optimistic-schema (instantiate-description-schema (:optimistic-schema hla) instance)
    :pessimistic-schema (instantiate-description-schema (:pessimistic-schema hla) instance)))

(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (let [hla-map (map-map (fn [[name hla]] [name (instantiate-strips-hla-schema hla instance)])
			 (safe-get hierarchy :hlas))
	act     (safe-get hla-map 'act)
	vacuous-desc (parse-description [:vac] :dummy :dummy)
	dummy-vars (for [[t v] (:vars act)] [(keyword (str "?" v)) [t]])]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy hla-map instance)
     (make-strips-hla-schema (gensym "strips-top-level-action") {} nil nil 
			     [[(gensym "strips-top-level-action-ref") nil nil
			       (map-map identity dummy-vars) 
			       (cons 'act (map first dummy-vars))]]
			     vacuous-desc vacuous-desc nil)  ; Dummy top-level action
     {}
     (make-conjunctive-condition nil nil)
     false
     )))

(comment 
  (instantiate-hierarchy
   (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		    (make-nav-switch-strips-domain))
   (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))

		    )

(defmethod hla-name                       ::StripsHLA [hla] 
  (cons (:name (:schema hla))
	(replace (:var-map hla) (:vars (:schema)))))

(defmethod hla-hierarchical-preconditions ::StripsHLA [hla]
  (:precondition hla))

(defmethod hla-optimistic-description     ::StripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (:var-map hla)))
  
(defmethod hla-pessimistic-description    ::StripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (:var-map hla)))

(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map skip-dummy?]
  (let [hla-vars (:vars hla)]
    (assert-is (= (count args) (count hla-vars)))
    (map-map (fn [arg hla-var] [hla-var (safe-get var-map arg)]) 
	     ((if skip-dummy? (partial filter (fn [arg var] (not (is-dummy-var? arg)))) identity)
	      (map #(vector %1 (second %2)) args hla-vars)))))

    

(defn- refinement-instantiations [precondition hierarchy expansion opt-val var-map dummy-var-vals]
  (if (empty? expansion)   ; must handle empty expansion specially
      (do (assert-is (empty? dummy-var-vals))
	  (assert-is (empty? var-map))
	  (when-not (dead-end-valuation? (restrict-valuation opt-val precondition))
	    ['()]))
    (let [hla-map      (safe-get hierarchy :hla-map),
	  first-action (safe-get hla-map (ffirst expansion)),
	  first-var-map (translate-var-map first-action (rfirst expansion) var-map true)
	  quasi-ground-first-precondition (conjoin-conditions
					   (make-conjunctive-condition
					    (map (partial simplify-atom first-var-map) (:pos-pre first-action))
					    (map (partial simplify-atom first-var-map) (:neg-pre first-action)))
					   precondition)]
      (for [dummy-var-map (valuation-consistent-mappings opt-val quasi-ground-first-precondition dummy-var-vals)]
	(let [final-var-map (merge var-map dummy-var-map)]
	  (map (fn [call extra-preconditions]
		 (let [hla (safe-get hla-map (first call))
		       trans-var-map (translate-var-map hla (rest call) final-var-map false)]
		   (make-strips-hla 
		    hierarchy 
		    hla 
		    trans-var-map 
		    (conjoin-conditions 
		     (make-conjunctive-condition
		      (map (partial simplify-atom trans-var-map) (safe-get hla :pos-pre)) 
		      (map (partial simplify-atom trans-var-map) (safe-get hla :neg-pre))) 
		     extra-preconditions)
		    (:primitive hla))))
	       expansion 
	       (cons (map (partial simplify-atom dummy-var-map) precondition)
		     (repeat (make-conjunctive-condition)))))))))

(prefer-method hla-immediate-refinements [::PrimitiveHLA ::Valuation] [::StripsHLA ::DNFSimpleValuation])

(defmethod hla-immediate-refinements     [::StripsHLA ::DNFSimpleValuation] [hla opt-val]
  (let [opt-val (restrict-valuation opt-val (:precondition hla))
	hierarchy (:hierarchy hla)
	objects   (:trans-objects (:problem-instance :hierarchy))
	var-map   (:var-map hla)]
    (when-not (dead-end-valuation? opt-val)
      (forcat [[name pos-pre neg-pre dummy-type-map expansion] (:refinement-schemata (:schema hla))]
	 (let [quasi-ground-impl-pre (make-conjunctive-condition
				      (map (partial simplify-atom var-map) pos-pre)
				      (map (partial simplify-atom var-map) neg-pre))
	       dummy-val-map (map-map (fn [var types] [var (forcat [t types] (safe-get objects t))]) 
				      dummy-type-map)]
	   (refinement-instantiations (conjoin-conditions quasi-ground-impl-pre (:precondition hla))
				      hierarchy
				      expansion
				      opt-val
				      var-map
				      dummy-val-map))))))

;	   (let [[impl-opt-val 
;	 (when-let [handled (handle-goal-preconditions 
;			       hierarchy
;			       (map (partial simplify-atom (:var-map hla)) expansion)
;			       )]
;	   (let [impl-opt-val (restrict-valuation 
;			       opt-val (make-conjunctive-condition (first handled) neg-pre))]
;	     (when-not (dead-end-valuation? impl-opt-val)
;	       (refinement-instantiations (conjoin-conditions impl-prec (:preconds hla))
;					  hierarchy
;					  expansion
;					  impl-opt-val
;					  (:var-map hla)
;					  (second handled))))))))))
		 
     

