;; This file defines valuations for hybrid problems, where we consider sets of 
;; (discrete dnf clause, continuous-lp-state) pairs.  

;; A corresponding kind of description, corresponding to a primitive, discrete-grounded
;; but continuous-ungrounded hybrid strips action, is also defined.

(ns edu.berkeley.ai.angelic.hybrid.dnf-lp-valuations
  (:use clojure.test edu.berkeley.ai.angelic
	[edu.berkeley.ai [ util :as util] [envs :as envs]]
	[edu.berkeley.ai.util [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]
	[edu.berkeley.ai.envs.hybrid-strips :as hs]
	[edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
	[edu.berkeley.ai.angelic.hybrid [continuous-lp-states :as cls]]))

(set! *warn-on-reflection* true)



(derive ::HybridDNFLPValuation :edu.berkeley.ai.angelic/Valuation)

(defstruct hybrid-dnf-lp-valuation-struct :class :clause-lp-set)

(defn make-hybrid-dnf-lp-valuation
  [clause-lp-pairs]
  (if (empty? clause-lp-pairs)
      *pessimal-valuation*
    (struct hybrid-dnf-lp-valuation-struct ::HybridDNFLPValuation (util/to-set clause-lp-pairs))))

(defmethod map->valuation ::HybridDNFLPValuation [type m]
  (if (empty? m) *pessimal-valuation*
    (make-hybrid-dnf-lp-valuation 
     (for [[[disc cont] rew] m]
       [(state->clause disc)
	(make-lp-state cont rew)]))))

(defmethod explicit-valuation-map ::HybridDNFLPValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation-max-reward ::HybridDNFLPValuation [val]
  (apply max (map #(last (cls/solve-lp-state (second %))) (:clause-lp-set val))))

(defmethod empty-valuation? ::HybridDNFLPValuation [val] false)

(defn restrict-hdlv-pair [clause-lp-pair condition]
  (hc/apply-constraint 
   clause-lp-pair
;   num var-map num-var-map objects constant-fns  ; TODO: ?????
   (fn [[d c] a] (when-let [nd (restrict-clause-pos d a)] [nd c]))
   (fn [[d c] a] (when-let [nd (restrict-clause-neg d a)] [nd c]))
   (fn [[d c] clm strict?] (when-let [nc (constrain-lp-state-lez c clm strict?)] [d nc]))
   (fn [[d c] clm]         (when-let [nc (constrain-lp-state-eqz c clm)] [d nc]))
   (fn [[d c] clm strict?] (when-let [nc (constrain-lp-state-gez c clm strict?)] [d nc]))))

(defmethod restrict-valuation [::HybridDNFLPValuation ::hc/ConstraintCondition] [val condition]
  (make-hybrid-dnf-lp-valuation
   (apply concat (map #(restrict-hdlv-pair % (util/safe-get condition :constraint)) (:clause-lp-set val)))))


(comment 

; Descriptions for primitives.
 ; :upper-reward-fn upper-reward-fn})
  (derive ::QuasigroundPrimitiveDescription :edu.berkeley.ai.angelic/Description)

  (defn make-quasiground-primitive-description [quasiground-action objects constant-fns]
    {:class ::QuasigroundPrimitiveDescription :objects objects :constant-fns constant-fns
     :action (assoc quasiground-action
               :num-var-map (util/map-map #(vector % (gensym (str %))) 
                                          (util/safe-get quasiground-action :num-vars)))})

  (defn- progress-qps [val desc]
                                        ;  (println (keys (:schema  (:action  desc))))
    (let [{:keys [action objects constant-fns]} desc
          {:keys [schema var-map num-var-map num]} action
          [adds deletes assignment-lm] (he/get-hybrid-effect-info (util/safe-get schema :effect) var-map num-var-map constant-fns)
          {:keys [discrete-state continuous-lp-states]} val
          reward-lm (util/map-vals - (le/hybrid-linear-expr->grounded-lm (util/safe-get schema :cost-expr) 
                                                                         var-map num-var-map constant-fns))]
      (make-hybrid-dnf-lp-valuation
       (reduce conj (reduce disj discrete-state deletes) adds)
       (for [cont continuous-lp-states
             cont (hc/apply-constraint (reduce (fn [c v] (cls/add-lp-state-param c v [] (get reward-lm v))) 
                                               cont (vals num-var-map))
                                       num var-map num-var-map objects constant-fns 
                                       (fn [s a] (when (contains? discrete-state a) s))
                                       (fn [s a] (when-not (contains? discrete-state a) s))
                                       cls/constrain-lp-state-lez cls/constrain-lp-state-eqz cls/constrain-lp-state-gez)]
         (cls/update-lp-state cont assignment-lm reward-lm)))))

  (defmethod progress-valuation 
    [::HybridDNFLPValuation ::QuasigroundPrimitiveDescription] 
    [val desc]
    (progress-qps val desc))



  (derive ::HybridFinishDescription ::QuasigroundPrimitiveDescription)

  (defn make-hybrid-finish-description [goal objects constant-fns]
    (assoc (make-quasiground-primitive-description  
            {:schema 
             {:effect (he/make-effect nil nil nil) :cost-expr {}} 
             :var-map {} :num-vars [] :num (util/safe-get goal :constraint)}
            objects constant-fns)
      :class ::HybridFinishDescription))

  (defn make-hybrid-finish-valuation [rew extra-keys]
    (merge extra-keys (map->valuation :edu.berkeley.ai.angelic.dnf-valuations/DNFSimpleValuation {*finish-state* rew})))


  (defmethod progress-valuation    [::HybridDNFLPValuation ::HybridFinishDescription] [val desc]
    (let [result (progress-qps val desc)]
      (if (empty-valuation? result) *pessimal-valuation*
          (make-hybrid-finish-valuation (valuation-max-reward val) result))))

;; TODO: fix
  (defmethod progress-valuation    [:edu.berkeley.ai.angelic/ConditionalValuation ::HybridFinishDescription] [val desc]
    (map->valuation :edu.berkeley.ai.angelic.dnf-valuations/DNFSimpleValuation {*finish-state* (valuation-max-reward val)}))



  (defn extract-fully-primitive-solution 
    "Take a solution (quasi-ground) primitive sequence and the final
   outcome, a hybrid-dnf-LP-valuation, and return a fully grounded
   sequence of hybrid-strips actions that achieves the optimal reward."
    [env act-seq]
    (let [action-space (:action-space env)
          objects      (util/safe-get env :objects)
          const-fns    (util/safe-get env :constant-numeric-vals)
          final-val    (reduce (fn [val act]
                                 (progress-valuation val
                                                     {:class ::QuasigroundPrimitiveDescription :objects objects :constant-fns const-fns :action act}))
                               (map->valuation ::HybridDNFLPValuation {(envs/get-initial-state env) 0})
                               act-seq)
          [cont-result num-var-map rew] (util/first-maximal-element #(nth % 2)
                                                                    (map #(cls/solve-lp-state %) (util/safe-get final-val :continuous-lp-states)))]
                                        ;    (println num-var-map)
      (map #(hs/hybrid-strips-action->action (:schema  %)
                                             (into (util/safe-get % :var-map) 
                                                   (for [nv (util/safe-get % :num-vars)] [nv (util/safe-get num-var-map (util/safe-get (:num-var-map %) nv))]))
                                             action-space) act-seq)))




  (set! *warn-on-reflection* false))