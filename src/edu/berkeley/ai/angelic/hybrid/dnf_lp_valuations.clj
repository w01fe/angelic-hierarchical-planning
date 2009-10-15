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

;; Assume this is only called for hierarchical preconditions.  
;; Assume everything is grounded, with no foralls, so we don't need any fancy business.
(defn restrict-hdlv-pair [clause-lp-pair constraint var-map num-var-map objects constant-fns]
  (hc/apply-constraint 
   clause-lp-pair
   constraint var-map num-var-map objects constant-fns
   (fn [[d c] a] (when-let [nd (restrict-clause-pos d a)] [nd c]))
   (fn [[d c] a] (when-let [nd (restrict-clause-neg d a)] [nd c]))
   (fn [[d c] clm strict?] (when-let [nc (constrain-lp-state-lez c clm strict?)] [d nc]))
   (fn [[d c] clm]         (when-let [nc (constrain-lp-state-eqz c clm)] [d nc]))
   (fn [[d c] clm strict?] (when-let [nc (constrain-lp-state-gez c clm strict?)] [d nc]))))

(defmethod restrict-valuation [::HybridDNFLPValuation ::hc/ConstraintCondition] [val condition]
  (make-hybrid-dnf-lp-valuation
   (apply concat (map #(restrict-hdlv-pair % (util/safe-get condition :constraint) :dummy :dummy :dummy :dummy) 
                      (:clause-lp-set val)))))


;; TODO!
(comment 
  (defmethod progress-valuation    [::HybridDNFLPValuation ::hybrid/HybridFinishDescription] [val desc]
    (let [{:keys [objects constant-fns goal]} desc
          result (progress-qps val   
                               (make-quasiground-primitive-description  
                                {:schema 
                                 {:effect (he/make-effect nil nil nil) :cost-expr {}} 
                                 :var-map {} :num-vars [] :num (util/safe-get goal :constraint)}
                                objects constant-fns))]
      (if (empty-valuation? result) *pessimal-valuation*
          (make-hybrid-finish-valuation (valuation-max-reward val) result)))))



  (set! *warn-on-reflection* false)