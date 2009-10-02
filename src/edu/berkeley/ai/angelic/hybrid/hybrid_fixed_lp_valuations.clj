;; This file defines valuations for hybrid problems, where the discrete part of the state
;; is always known but we may be angelic about the continuous part.  

;; In particular, a hybrid-fixed-lp-valuation consists of a set of true discrete propositions,
;; together with a continuous-lp-state for the continuous variables.  

;; A corresponding kind of description, corresponding to a primitive, discrete-grounded
;; but continuous-ungrounded hybrid strips action, is also defined.

(ns edu.berkeley.ai.angelic.hybrid.hybrid-fixed-lp-valuations
  (:use clojure.test 
	[edu.berkeley.ai.util :as util]
	[edu.berkeley.ai.util [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]
	[edu.berkeley.ai.envs.hybrid-strips [hybrid-constraints :as hc] [hybrid-effects :as he]]
	[edu.berkeley.angelic.hybrid [continuous-lp-states :as cls]]))

(set! *warn-on-reflection* true)


; To potentially combine LPs, need: 
;   Bigger feasible region, & dominated reward over intersection.

(derive ::HybridFixedLPValuation :edu.berkeley.ai.angelic/Valuation)

(defstruct hybrid-fixed-lp-valuation-struct :class :discrete-state :continuous-lp-states)

(defn make-hybrid-fixed-lp-valuation
  "Take an assignment from all state variables to numeric values, and make a fresh
   lp-state.  A new variable called [:reward] will be assumed, with val 0, unless provided."
  [discrete-state continuous-lp-states]
  (if (empty? continuous-lp-states)
      *pessimal-valuation*
    (struct hybrid-fixed-lp-valuation-struct ::HybridFixedLPValuation discrete-state continuous-lp-states)))
  

(defmethod map->valuation ::HybridFixedLPValuation [type m]
  (if (empty? m) *pessimal-valuation*
    (let [disc-states (map first (keys m))]
      (assert (apply = disc-states))
      (make-hybrid-fixed-lp-valuation 
       (first disc-states)
       (for [[[disc cont] rew] m]
	 (make-lp-state cont rew))))))

(defmethod explicit-valuation-map ::HybridFixedLPValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation-max-reward ::HybridFixedLPValuation [val]
  (apply max (map #(last (cls/solve-lp-state %)) (:continuous-lp-states val))))



;(defmethod restrict-valuation [::HybridFixedLPValuation ...] [val condition]
  ; constrain-lp-state-??z
;  )




; Descriptions for primitives.
 ; :upper-reward-fn upper-reward-fn})

(defn make-quasiground-primitive-description [quasiground-action objects constant-fns]
  {:class ::QuasigroundPrimitiveDescription :objects objects :constant-fns constant-fns
   :action (assoc quasiground-action
	     :num-var-map (util/map-map #(vector % (atom nil)) 
					(util/safe-get quasiground-action :num-vars)))})

(defmethod progress-valuation 
  [::HybridFixedLPValuation ::QuasigroundPrimitiveDescription] 
  [val desc]
  (let [{:keys [action objects constant-fns]} (:action desc)
	{:keys [schema var-map num-var-map num]} action
	[adds deletes assignment-lm] (he/get-hybrid-effect-info (util/safe-get schema :effect) var-map)
	{:keys [discrete-state continuous-lp-states]} val]
    (make-hybrid-fixed-lp-valuation
     (apply assoc (apply dissoc discrete-state (simplify deletes)) (simplify adds))
     (for [cont continuous-lp-states
	   cont (hc/apply-constraint (reduce cls/add-lp-state-param cont (vals num-var-map))
				  num var-map num-var-map objects constant-fns 
				  (fn [s a] (when (contains? discrete-state a) s))
				  (fn [s a] (when-not (contains? discrete-state a) s))
				  cls/constrain-lp-state-leq cls/constrain-lp-state-eqz cls/constrain-lp-state-gez)]
       (cljs/update-lp-state cont assignment-lm 
	 (util/map-vals - (le/hybrid-linear-expr->grounded-lm (util/safe-get schema :cost-expr) 
							   var-map num-var-map constant-fns)))))))


(defn extract-fully-primitive-solution 
  "Take a solution (quasi-ground) primitive sequence and the final
   outcome, a hybrid-fixed-LP-valuation, and return a fully grounded
   sequence of hybrid-strips actions that achieves the optimal reward."
  [env act-seq]
  (let [action-space (:action-space env)
	objects      (util/safe-get env :objects)
	const-fns    (util/safe-get env :constant-numeric-vals)
	final-val    (reduce (fn [val act]
			       (progress-valation val
			         {:class ::QuasigroundPrimitiveDescription :objects objects :constant-fns const-fns :action act}))
			     act-seq)
	[cont-result num-var-map rew] (util/first-maximal-element #(nth % 2)
				       (map #(cls/solve-lp-state %) (util/safe-get final-val :continous-lp-states)))]
    (map #(hybrid-action->action %
	   (into (util/safe-get % :var-map) 
		 (for [nv (safe-get % :num-vars)] [nv (util/safe-get num-var-map nv)]))
	   action-space) act-seq)))




(set! *warn-on-reflection* false)