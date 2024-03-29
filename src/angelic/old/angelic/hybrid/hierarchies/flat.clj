(ns angelic.old.angelic.hybrid.hierarchies.flat
  (:use angelic.old.angelic angelic.old.angelic.hierarchies
        angelic.old.angelic.hybrid)
  (:require [angelic.util :as util] [angelic.old  [envs :as envs]]
	    [angelic.util [linear-expressions :as le]]
	    [angelic.old.envs.hybrid-strips :as hs]
	    [angelic.old.envs.hybrid-strips 
	     [constraints :as hc]
	     [effects :as he]]
	    [angelic.old.angelic.hybrid 
	     [fixed-lp-valuations :as hflv]])
  )

;; Flat hybrid hierarchies, which do a usual primitive forward search
;; but are angelic about continuous parameters to the "primitives".

;; TODO: two versions, with and without "splitting."
;; Splitting is complex in full angelic setting, but trivial here ...

;;; Flat hierarchy

(defstruct hybrid-flat-hierarchy-schema :class  :upper-reward-fn)
(defn make-hybrid-flat-hierarchy-schema [upper-reward-fn]
  (struct hybrid-flat-hierarchy-schema ::HybridFlatHierarchySchema upper-reward-fn))

(defn get-hybrid-flat-hierarchy 
  "Upper-reward-function should map a valuation to an upper bound on *total* reward to goal"
;  ([env] (instantiate-hierarchy (make-hybrid-flat-hierarchy-schema) env)))
  ([env] (get-hybrid-flat-hierarchy env valuation-max-reward))
  ([env upper-reward-fn]
   (instantiate-hierarchy (make-hybrid-flat-hierarchy-schema upper-reward-fn) env)))

(defstruct hybrid-flat-act-hla :class :env :opt-desc :action-space)
(defn- make-hybrid-flat-act-hla [env opt-desc action-space]
  (struct hybrid-flat-act-hla ::HybridFlatActHLA env opt-desc action-space))

(defstruct hybrid-flat-primitive-hla :class :env :desc)
(defn- make-hybrid-flat-primitive-hla [env action]
  (struct hybrid-flat-primitive-hla ::HybridFlatPrimitiveHLA env
	  (hflv/make-quasiground-primitive-description action 
	    (util/safe-get env :objects) (util/safe-get env :constant-numeric-vals))))

(defstruct hybrid-flat-finish-hla :class :desc :env)
(derive ::HybridFlatFinishHLA ::HybridFlatPrimitiveHLA)
(defn- make-hybrid-flat-finish-hla [env]
  (struct hybrid-flat-finish-hla ::HybridFlatFinishHLA 
    (instantiate-description-schema *hybrid-finish-description-schema* env)))


; Special descriptions for Act.

(defn make-hybrid-flat-act-optimistic-description [goal upper-reward-fn]
  {:class ::HybridFlatActOptimisticDescription :goal goal  :upper-reward-fn upper-reward-fn})

(defmethod progress-valuation [:angelic.old.angelic/Valuation ::HybridFlatActOptimisticDescription] [val desc]
  (make-conditional-valuation 
   (:goal desc)
   ((:upper-reward-fn desc) val)))
   



(defmethod instantiate-hierarchy ::HybridFlatHierarchySchema [hierarchy instance]
  [(make-hybrid-flat-act-hla 
    instance 
    (make-hybrid-flat-act-optimistic-description 
     (envs/get-goal instance) (:upper-reward-fn hierarchy))
    (envs/get-action-space instance))
   (make-hybrid-flat-finish-hla instance)])

(defmethod hla-default-optimistic-valuation-type ::HybridFlatActHLA [hla] 
  ::hflv/HybridFixedLPValuation)

(defmethod hla-default-pessimistic-valuation-type ::HybridFlatActHLA [hla] 
  ::hflv/HybridFixedLPValuation)

(defmethod hla-primitive? ::HybridFlatPrimitiveHLA [hla] true)
(defmethod hla-primitive ::HybridFlatPrimitiveHLA [hla] (util/safe-get (:desc hla) :action))
(defmethod hla-primitive ::HybridFlatFinishHLA [hla] :noop)

(defmethod hla-primitive? ::HybridFlatActHLA [hla] false)
(defmethod hla-primitive ::HybridFlatActHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-name ::HybridFlatPrimitiveHLA [hla] 
  (let [a (:action (:desc hla))
	s (util/safe-get a :schema)]
    (vec (cons (:name s)
	       (concat (map (:var-map a)  (util/difference (set (map second  (:vars s))) (set (:num-vars a))))
		       (vals (:num-var-map a)))))))
(defmethod hla-name ::HybridFlatFinishHLA [hla] 'finish)
(defmethod hla-name ::HybridFlatActHLA [hla] 'act)

(defmethod hla-immediate-refinements [::HybridFlatPrimitiveHLA :angelic.old.angelic/Valuation] [hla val] nil)
(defmethod hla-immediate-refinements [::HybridFlatActHLA ::hflv/HybridFixedLPValuation]            [hla val]
  (cons [] 
	(for [action ((util/safe-get (:action-space hla) :discrete-generator) (util/safe-get val :discrete-state))]
	  [(make-hybrid-flat-primitive-hla (:env hla) action) hla])))


(defmethod hla-hierarchical-preconditions ::HybridFlatPrimitiveHLA [hla] 
  envs/*true-condition*) 
(defmethod hla-hierarchical-preconditions ::HybridFlatActHLA [hla] 
  envs/*true-condition*) 

(defmethod hla-optimistic-description ::HybridFlatPrimitiveHLA [hla] (:desc hla))

(defmethod hla-optimistic-description ::HybridFlatFinishHLA [hla]
  (util/safe-get hla :desc))

(defmethod hla-optimistic-description ::HybridFlatActHLA [hla] 
  (:opt-desc hla))

(defmethod hla-pessimistic-description ::HybridFlatPrimitiveHLA [hla] (:desc hla))

(defmethod hla-pessimistic-description ::HybridFlatFinishHLA [hla]
  (util/safe-get hla :desc))

(defmethod hla-pessimistic-description ::HybridFlatActHLA [hla] 
  *pessimal-description*)

(defmethod hla-environment ::HybridFlatActHLA [hla] (util/safe-get hla :env))
(defmethod hla-environment ::HybridFlatPrimitiveHLA [hla] (util/safe-get hla :env))

(comment
  
  (let [e (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])]
    (map :name (extract-hybrid-primitive-solution e 
                 (first (interactive-search (alt-node (get-hybrid-flat-hierarchy e (make-hybrid-blocks-heuristic e))
                                                 {:cache? false :graph? false :ref-choice-fn first-choice-fn}))))))
  )