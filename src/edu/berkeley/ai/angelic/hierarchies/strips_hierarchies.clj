(ns edu.berkeley.ai.angelic.hierarchies.strips-hierarchies
  (:refer-clojure)
  (:use [edu.berkeley.ai.util :as util] edu.berkeley.ai.util.propositions edu.berkeley.ai.domains.strips edu.berkeley.ai.angelic edu.berkeley.ai.angelic.ncstrips-descriptions edu.berkeley.ai.angelic.hierarchies)
  )

; Immediate refinements are [pos-prec neg-prec expansion]

; TODO TODO: hangle goal-match.  
; TODO: handle :?
; TODO: handle top-level (specialized code?)

(defstruct strips-hla-schema :class :name :vars :pos-pre :neg-pre :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)



(defn make-strips-hla-schema [name parameters pos-preconditions neg-preconditions refinement-schemata optimistic-schema pessimistic-schema primitive]
  (struct strips-hla-schema ::StripsHLASchema name parameters pos-preconditions neg-preconditions 
	  refinement-schemata optimistic-schema pessimistic-schema primitive))

(defn- check-hla-expansion [types vars-and-objects all-actions expansion]
  (for [action expansion]
    (let [params (rest action)
	  declared-types (safe-get all-actions (first action))]
      (assert-is (= (count params) (count declared-types)))
      (cons (first action)
	    (for [[par type] (map vector params declared-types)]
	      (do (or (= par :?) (check-type types vars-and-objects par type))
		  par))))))

(defn- check-hla-schema [types guaranteed-objs predicates all-actions hla-schema] 
;  (.println System/out action-schema)
  (assert-is (not (map? (:vars hla-schema))))
  (let [vars-and-objects (check-objects types (concat guaranteed-objs (:vars hla-schema)))
	atom-checker (fn [atoms] (map #(check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-hla-schema 
     (:name hla-schema)
     (:vars hla-schema)
     (atom-checker (:pos-pre hla-schema))
     (atom-checker (:neg-pre hla-schema))
     (map (fn [[pos-pre neg-pre expansion]]
	    [(atom-checker pos-pre)
	     (atom-checker neg-pre)
	     (check-hla-expansion types vars-and-objects all-actions expansion)])
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
	    [:optional [:pessimistic  [unquote pessimistic]]]}
	  (chunk 2 (rest hla))]
    (let [[pos-pre neg-pre] (parse-pddl-conjunction precondition)
	   params        (parse-typed-pddl-list parameters)] 
      (make-strips-hla-schema
       (first hla)
       params
       pos-pre
       neg-pre
       (map (fn [refinement]
	      (match [[[:optional [:precondition [unquote precondition]]]
		       [:expansion [unquote expansion]]]
		      (chunk 2 refinement)]
		(let [[pp np] (parse-pddl-conjunction precondition)] 
		  [pp np expansion])))
	    refinements)
       (parse-description optimistic domain params)
       (parse-description pessimistic domain params)
       nil))))
     


;   (assert-is (isa? (:class env) ::StripsPlanningDomain))
;  (let [types      (:types domain) 
;	objects    (:guaranteed-objs domain)
;	predicates (:predicates domain)
;	actions    (:action-schemata domain)]
	     

(defmethod parse-hierarchy-type :strips-hierarchy [type contents domain]
  (assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (match [[[:multiple (:hla [unquote-seq hlas])]] contents]
    {:class :StripsHierarchy, :hlas
     (check-hla-schemata (:types domain) (:guaranteed-objs domain) (:predicates domain) (:action-schemata domain)
			 (map #(parse-strips-hla-schema % domain) hlas))}))
      

(comment 
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
		   (make-nav-switch-strips-domain))

		    )








(derive ::StripsHLA ::HLA)
(derive ::StripsParamHLA ::StripsHLA)
(derive ::StripsPrimitiveHLA ::StripsHLA)
(derive ::StripsPrimitiveHLA ::PrimitiveHLA)

(defmethod instantiate-hierarchy ::StripsHLASchema [top-level-action instance] 
  (assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  ; TODO: instantiate descriptions
  ; TODO: maintain state.
  top-level-action
  )


(defstruct strips-hla :class :schema :var-map)
(defstruct strips-param-hla :class :schema :var-map)

(defmethod hla-name                       ::StripsHLA [hla]
  )

(defmethod hla-immediate-refinements     [::StripsHLA ::DNFSimpleValuation] [hla opt-val]
  )

(defmethod hla-hierarchical-preconditions ::StripsHLA [hla]
  )

(defmethod hla-optimistic-description     ::StripsHLA [hla]
  )
  
(defmethod hla-pessimistic-description    ::StripsHLA [hla]
  )

