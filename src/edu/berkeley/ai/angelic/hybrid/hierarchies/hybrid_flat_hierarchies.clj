(ns edu.berkeley.ai.angelic.hierarchies.flat-hierarchies
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
	    [edu.berkeley.ai.util [linear-expressions :as le]]
	    [edu.berkeley.ai.envs.hybrid-strips :as hs]
	    [edu.berkeley.ai.envs.hybrid-strips 
	     [hybrid-constraints :as hc]
	     [hybrid-effects :as he]]
	    [edu.berkeley.ai.angelic.hybrid 
	     [hybrid_fixed_lp_valuations :as hflv]])
  )

;; Flat hybrid hierarchies, which do a usual primitive forward search
;; but are angelic about continuous parameters to the "primitives".

;; TODO: two versions, with and without "splitting."
;; Splitting is complex in full angelic setting, but trivial here ...

;;; Flat hierarchy

(defstruct hybrid-flat-hierarchy-schema :class #_ :upper-reward-fn)
(defn make-hybrid-flat-hierarchy-schema [#_upper-reward-fn]
  (struct hybrid-flat-hierarchy-schema ::HybridFlatHierarchySchema)); upper-reward-fn))

(defn get-hybrid-flat-hierarchy 
  ([env] (instantiate-hierarchy (make-hybrid-flat-hierarchy-schema) env)))
;  ([env] (get-hybrid-flat-hierarchy env (constantly 0))))
;  ([env upper-reward-fn]
;   (instantiate-hierarchy (make-hybrid-flat-hierarchy-schema upper-reward-fn) env)))

(defstruct hybrid-flat-act-hla :class :env :opt-desc :action-space)
(defn- make-hybrid-flat-act-hla [env opt-desc action-space]
  (struct hybrid-flat-act-hla ::HybridFlatActHLA env opt-desc action-space))

(defstruct hybrid-flat-primitive-hla :class :action :env)
(defn- make-hybrid-flat-primitive-hla [env action]
  (struct hybrid-flat-primitive-hla ::HybridFlatPrimitiveHLA action env))

(defstruct hybrid-flat-finish-hla :class :desc :env)
(derive ::HybridFlatFinishHLA ::HybridFlatPrimitiveHLA)
(defn- make-hybrid-flat-finish-hla [env]
  (struct hybrid-flat-finish-hla ::HybridFlatFinishHLA 
	  (instantiate-description-schema *finish-description* env) env))

(defn fully-ground-hybrid-solution [hlas final-val]
  (assert (seq hlas))
  ...)

; Special descriptions for Act.

(defn make-hybrid-flat-act-optimistic-description [goal #_upper-reward-fn]
  {:class ::HybridFlatActOptimisticDescription :goal goal}) ; :upper-reward-fn upper-reward-fn})

(defmethod progress-valuation [:edu.berkeley.ai.angelic/Valuation ::HybridFlatActOptimisticDescription] [val desc]
;  (let [state-map (explicit-valuation-map val)]
;    (util/assert-is (= (count state-map) 1))
;    (let [[prev-state prev-reward] (first state-map)]
      (make-conditional-valuation 
       (:goal desc)
       (valuation-max-reward val)))
;       (+ prev-reward ((:upper-reward-fn desc) prev-state))))))
   



(defmethod instantiate-hierarchy ::HybridFlatHierarchySchema [hierarchy instance]
  [(make-hybrid-flat-act-hla 
    instance 
    (make-hybrid-flat-act-optimistic-description 
     (envs/get-goal instance) #_(:upper-reward-fn hierarchy))
    (envs/get-action-space instance))
   (make-hybrid-flat-finish-hla instance)])

(defmethod hla-default-optimistic-valuation-type ::HybridFlatActHLA [hla] 
  ::hflv/HybridFixedLPValuation)

(defmethod hla-default-pessimistic-valuation-type ::HybridFlatActHLA [hla] 
  ::hflv/HybridFixedLPValuation)

(defmethod hla-primitive? ::HybridFlatPrimitiveHLA [hla] true)
(defmethod hla-primitive ::HybridFlatPrimitiveHLA [hla] (:action hla))
(defmethod hla-primitive ::HybridFlatFinishHLA [hla] :noop)

(defmethod hla-primitive? ::HybridFlatActHLA [hla] false)
(defmethod hla-primitive ::HybridFlatActHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-name ::HybridFlatPrimitiveHLA [hla] (:name (:action hla)))
(defmethod hla-name ::HybridFlatFinishHLA [hla] 'finish)
(defmethod hla-name ::HybridFlatActHLA [hla] 'act)

(defmethod hla-immediate-refinements [::HybridFlatPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla val] nil)
(defmethod hla-immediate-refinements [::HybridFlatActHLA ::hflv/HybridFixedLPValuation]            [hla val]
  (cons [] 
	(for [action ((util/safe-get (:action-space hla) :discrete-generator) (util/safe-get val :discrete-state))]
	  [(make-hybrid-flat-primitive-hla (:env hla) action) hla])))))


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

