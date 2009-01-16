(in-ns 'edu.berkeley.ai.angelic.hierarchies)

;; Flat hierarchies, which adapt either ordinary domains or STRIPS domains (mostly for efficiency comparison) for hierarchical search.  
; In particular, Act --> [Prim Act] or [] (reg. of if at goal)

;;; Flat hierarchy

(defstruct flat-hierarchy-schema :class :upper-reward-fn)
(defn make-flat-hierarchy-schema [upper-reward-fn]
  (struct flat-hierarchy-schema ::FlatHierarchySchema upper-reward-fn))

(defstruct flat-act-hla :class :env :opt-desc)
(derive ::FlatActHLA ::HLA)
(defn- make-flat-act-hla [env opt-desc]
  (struct flat-act-hla ::FlatActHLA env opt-desc))

(defstruct flat-primitive-hla :class :action :env)
(derive ::FlatPrimitiveHLA ::HLA)
(defn- make-flat-primitive-hla [env action]
  (struct flat-primitive-hla ::FlatPrimitiveHLA action env))


; Special descriptions for Act.

(defn make-flat-act-optimistic-description [goal upper-reward-fn]
  {:class ::FlatActOptimisticDescription :goal goal :upper-reward-fn upper-reward-fn})

(defmethod progress-optimistic [:edu.berkeley.ai.angelic/Valuation ::FlatActOptimisticDescription] [val desc]
  (let [state-map (explicit-valuation-map val)]
    (util/assert-is (= (count state-map) 1))
    (let [[prev-state prev-reward] (first state-map)]
      (make-conditional-valuation 
       (:goal desc)
       (+ prev-reward ((:upper-reward-fn desc) prev-state))))))
   
(defmethod progress-pessimistic [:edu.berkeley.ai.angelic/Valuation ::FlatActOptimisticDescription] [val desc]
  (throw (UnsupportedOperationException.)))



(defmethod instantiate-hierarchy ::FlatHierarchySchema [hierarchy instance]
  (make-flat-act-hla 
   instance 
   (make-flat-act-optimistic-description (envs/get-goal instance) (:upper-reward-fn hierarchy))))


(defmethod hla-primitive ::FlatPrimitiveHLA [hla] (:action hla))
(defmethod hla-primitive ::FlatActHLA [hla] nil)

(defmethod hla-name ::FlatPrimitiveHLA [hla] (:name (:action hla)))
(defmethod hla-name ::FlatActHLA [hla] 'act)

(defmethod hla-immediate-refinements [::FlatPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla val] nil)
(defmethod hla-immediate-refinements [::FlatActHLA :edu.berkeley.ai.angelic/Valuation]       [hla val]
  (let [state-map (explicit-valuation-map val)]
    (util/assert-is (= (count state-map) 1))
    (let [[prev-state prev-reward] (first state-map)]
      (cons [] 
	    (for [action (envs/applicable-actions prev-state (envs/get-action-space (:env hla)))]
	      [(make-flat-primitive-hla (:env hla) action) hla])))))
;	(if (envs/satisfies-condition? prev-state (envs/get-goal (:env hla)))
;	    (cons [] prim-act-refs)
;	  prim-act-refs)))))

(defmethod hla-hierarchical-preconditions ::FlatPrimitiveHLA [hla] 
  envs/*true-condition*) ;TODO??
(defmethod hla-hierarchical-preconditions ::FlatActHLA [hla] 
  envs/*true-condition*) 

(defmethod hla-optimistic-description ::FlatPrimitiveHLA [hla]
  (make-explicit-description (envs/make-enumerated-action-space [(:action hla)])))

(defmethod hla-optimistic-description ::FlatActHLA [hla] 
  (:opt-desc hla))

(defmethod hla-pessimistic-description ::FlatPrimitiveHLA [hla] 
  (make-explicit-description (envs/make-enumerated-action-space [(:action hla)])))

(defmethod hla-pessimistic-description ::FlatActHLA [hla] 
  *pessimal-description*)


