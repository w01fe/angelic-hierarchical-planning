(ns edu.berkeley.ai.angelic.hierarchies.flat-hierarchies
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]])
  )

;; Flat hybrid hierarchies, which do a usual primitive forward search
;; but are angelic about continuous parameters to the "primitives".

;;; Flat hierarchy

(defstruct hybrid-flat-hierarchy-schema :class :upper-reward-fn)
(defn make-hybrid-flat-hierarchy-schema [upper-reward-fn]
  (struct hybrid-flat-hierarchy-schema ::HybridFlatHierarchySchema upper-reward-fn))

(defn get-hybrid-flat-hierarchy 
  ([env] (get-hybrid-flat-hierarchy env (constantly 0)))
  ([env upper-reward-fn]
   (instantiate-hierarchy (make-hybrid-flat-hierarchy-schema upper-reward-fn) env)))

(defstruct flat-act-hla :class :env :opt-desc :action-space)
;(derive ::HybridFlatActHLA ::HLA)
(defn- make-flat-act-hla [env opt-desc action-space]
  (struct flat-act-hla ::HybridFlatActHLA env opt-desc action-space))

(defstruct flat-primitive-hla :class :action :env)
;(derive ::HybridFlatPrimitiveHLA ::HLA)
(defn- make-flat-primitive-hla [env action]
  (struct flat-primitive-hla ::HybridFlatPrimitiveHLA action env))

(defstruct flat-finish-hla :class :desc :env)
(derive ::HybridFlatFinishHLA ::HybridFlatPrimitiveHLA)
(defn- make-flat-finish-hla [env]
  (struct flat-finish-hla ::HybridFlatFinishHLA (instantiate-description-schema *finish-description* env) env))


; Special descriptions for Act.

(defn make-flat-act-optimistic-description [goal upper-reward-fn]
  {:class ::HybridFlatActOptimisticDescription :goal goal :upper-reward-fn upper-reward-fn})

(defmethod progress-valuation [:edu.berkeley.ai.angelic/Valuation ::HybridFlatActOptimisticDescription] [val desc]
  (let [state-map (explicit-valuation-map val)]
    (util/assert-is (= (count state-map) 1))
    (let [[prev-state prev-reward] (first state-map)]
      (make-conditional-valuation 
       (:goal desc)
       (+ prev-reward ((:upper-reward-fn desc) prev-state))))))
   


(defmethod instantiate-hierarchy ::HybridFlatHierarchySchema [hierarchy instance]
  [(make-flat-act-hla 
    instance 
    (make-flat-act-optimistic-description (envs/get-goal instance) (:upper-reward-fn hierarchy))
    (envs/get-action-space instance))
   (make-flat-finish-hla instance)])

(defmethod hla-default-optimistic-valuation-type ::HybridFlatActHLA [hla] 
  :edu.berkeley.ai.angelic/ExplicitValuation)

(defmethod hla-default-pessimistic-valuation-type ::HybridFlatActHLA [hla] 
  :edu.berkeley.ai.angelic/ExplicitValuation)

(defmethod hla-primitive? ::HybridFlatPrimitiveHLA [hla] true)
(defmethod hla-primitive ::HybridFlatPrimitiveHLA [hla] (:action hla))
(defmethod hla-primitive ::HybridFlatFinishHLA [hla] :noop)

(defmethod hla-primitive? ::HybridFlatActHLA [hla] false)
(defmethod hla-primitive ::HybridFlatActHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-name ::HybridFlatPrimitiveHLA [hla] (:name (:action hla)))
(defmethod hla-name ::HybridFlatFinishHLA [hla] 'finish)
(defmethod hla-name ::HybridFlatActHLA [hla] 'act)

(defmethod hla-immediate-refinements [::HybridFlatPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla val] nil)
(defmethod hla-immediate-refinements [::HybridFlatActHLA :edu.berkeley.ai.angelic/Valuation]       [hla val]
  (let [state-map (explicit-valuation-map val)]
    (util/assert-is (= (count state-map) 1))
    (let [[prev-state prev-reward] (first state-map)]
      (cons [] 
	    (for [action (envs/applicable-actions prev-state (:action-space hla))]
	      [(make-flat-primitive-hla (:env hla) action) hla])))))
;	(if (envs/satisfies-condition? prev-state (envs/get-goal (:env hla)))
;	    (cons [] prim-act-refs)
;	  prim-act-refs)))))

(defmethod hla-hierarchical-preconditions ::HybridFlatPrimitiveHLA [hla] 
  envs/*true-condition*) 
(defmethod hla-hierarchical-preconditions ::HybridFlatActHLA [hla] 
  envs/*true-condition*) 

(defmethod hla-optimistic-description ::HybridFlatPrimitiveHLA [hla]
  (make-explicit-description (envs/make-enumerated-action-space [(:action hla)])))

(defmethod hla-optimistic-description ::HybridFlatFinishHLA [hla]
  (util/safe-get hla :desc))

(defmethod hla-optimistic-description ::HybridFlatActHLA [hla] 
  (:opt-desc hla))

(defmethod hla-pessimistic-description ::HybridFlatPrimitiveHLA [hla] 
  (make-explicit-description (envs/make-enumerated-action-space [(:action hla)])))

(defmethod hla-pessimistic-description ::HybridFlatFinishHLA [hla]
  (util/safe-get hla :desc))

(defmethod hla-pessimistic-description ::HybridFlatActHLA [hla] 
  *pessimal-description*)

(defmethod hla-environment ::HybridFlatActHLA [hla] (util/safe-get hla :env))
(defmethod hla-environment ::HybridFlatPrimitiveHLA [hla] (util/safe-get hla :env))

