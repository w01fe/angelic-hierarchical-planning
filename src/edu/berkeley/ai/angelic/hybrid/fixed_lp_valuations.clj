;; This file defines valuations for hybrid problems, where the discrete part of the state
;; is always known but we may be angelic about the continuous part.  

;; In particular, a hybrid-fixed-lp-valuation consists of a set of true discrete propositions,
;; together with a continuous-lp-state for the continuous variables.  

;; A corresponding kind of description, corresponding to a primitive, discrete-grounded
;; but continuous-ungrounded hybrid strips action, is also defined.

(ns edu.berkeley.ai.angelic.hybrid.fixed-lp-valuations
  (:use clojure.test edu.berkeley.ai.angelic [edu.berkeley.ai.angelic.hybrid :as hybrid]
	[edu.berkeley.ai [ util :as util] [envs :as envs]]
	[edu.berkeley.ai.util  [linear-expressions :as le]]
	[edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
	[edu.berkeley.ai.angelic.hybrid [continuous-lp-states :as cls]]))

(set! *warn-on-reflection* true)


; To potentially combine LPs, need: 
;   Bigger feasible region, & dominated reward over intersection.
;; TODO: do seomthing smarter about duplicates

(derive ::HybridFixedLPValuation :edu.berkeley.ai.angelic/Valuation)

(defstruct hybrid-fixed-lp-valuation-struct :class :discrete-state :continuous-lp-states)

(defn make-hybrid-fixed-lp-valuation
  [discrete-state continuous-lp-states]
  (if (empty? continuous-lp-states)
      *pessimal-valuation*
      (struct hybrid-fixed-lp-valuation-struct ::HybridFixedLPValuation discrete-state (util/to-set  continuous-lp-states))))
  

(defmethod map->valuation ::HybridFixedLPValuation [type m]
  (if (empty? m) *pessimal-valuation*
    (let [disc-states (map first (keys m))]
      (assert (apply = disc-states))
      (make-hybrid-fixed-lp-valuation 
       (first disc-states)
       (for [[[disc cont] rew] m]
	 (make-lp-state cont true rew))))))

(defmethod explicit-valuation-map ::HybridFixedLPValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation-max-reward ::HybridFixedLPValuation [val]
;  (println "Solving Lps:" (count (:continuous-lp-states val)))
  (apply max 
    Double/NEGATIVE_INFINITY
    (util/map-when #(last (cls/solve-lp-state %)) (:continuous-lp-states val))))

(defmethod empty-valuation? ::HybridFixedLPValuation [val] false)



; Descriptions for primitives.
 ; :upper-reward-fn upper-reward-fn})
(derive ::QuasigroundPrimitiveDescription :edu.berkeley.ai.angelic/Description)

(defn make-quasiground-primitive-description 
  ([quasiground-action objects constant-fns]
     (make-quasiground-primitive-description quasiground-action objects constant-fns 
       (util/map-map #(vector % (gensym (str %))) 
                     (util/safe-get quasiground-action :num-vars))))
  ([quasiground-action objects constant-fns num-var-map]
     {:class ::QuasigroundPrimitiveDescription :objects objects :constant-fns constant-fns
      :action (assoc quasiground-action :num-var-map num-var-map)}))

(defn- progress-qps [val desc]
;  (println (keys (:schema  (:action  desc))))
  (let [{:keys [action objects constant-fns]} desc
	{:keys [schema var-map num-var-map num]} action
	[adds deletes assignment-lm] (he/get-hybrid-effect-info (util/safe-get schema :effect) var-map num-var-map constant-fns)
	{:keys [discrete-state continuous-lp-states]} val
	reward-lm (util/map-vals - (le/hybrid-linear-expr->grounded-lm (util/safe-get schema :cost-expr) 
								       var-map num-var-map constant-fns))]
    (make-hybrid-fixed-lp-valuation
     (reduce conj (reduce disj discrete-state deletes) adds)
     (for [cont continuous-lp-states
	   cont (hc/apply-constraint (reduce (fn [c v] (cls/add-lp-state-param c v [] (get reward-lm v))) 
					     cont (vals num-var-map))
				  num var-map num-var-map objects constant-fns 
				  (fn [s a] (when (contains? discrete-state a) s))
				  (fn [s a] (when-not (contains? discrete-state a) s))
				  cls/constrain-lp-state-lez cls/constrain-lp-state-eqz cls/constrain-lp-state-gez
                                  cls/lp-state-feasible?)]
       (cls/update-lp-state cont assignment-lm reward-lm)))))


(defmethod progress-valuation 
  [::HybridFixedLPValuation ::QuasigroundPrimitiveDescription] 
  [val desc]
  (progress-qps val desc))


(defmethod progress-valuation    [::HybridFixedLPValuation ::hybrid/HybridFinishDescription] [val desc]
  (let [{:keys [objects constant-fns goal]} desc
        result (progress-qps val   
                 (make-quasiground-primitive-description  
                  {:schema 
                   {:effect (he/make-effect nil nil nil) :cost-expr {}} 
                   :var-map {} :num-vars [] :num (util/safe-get goal :constraint)}
                  objects constant-fns))]
    (if (empty-valuation? result) *pessimal-valuation*
      (make-hybrid-finish-valuation (valuation-max-reward val) result))))






(set! *warn-on-reflection* false)


(comment 



;(defn restrict-hflv-clp [cont disc constraint]
;  (hc/apply-constraint cont
;     num var-map num-var-map objects constant-fns  ; TODO: ?????
;     (fn [s a] (when (contains? disc a) s))
;     (fn [s a] (when-not (contains? disc a) s))
;     cls/constrain-lp-state-lez cls/constrain-lp-state-eqz cls/constrain-lp-state-gez))

;(defmethod restrict-valuation [::HybridFixedLPValuation ::hc/ConstraintCondition] [val condition]
;  (make-hybrid-fixed-lp-valuation
;   (:discrete-state val)
;   (apply concat (map #(restrict-hflv-clp % (:discrete-state val) (util/safe-get condition :constraint)) 
;		      (:continuous-lp-states val)))))


)