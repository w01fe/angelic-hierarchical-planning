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


;; Hierarchical preconditions must consist of fully grounded atoms
;; and grounded or quasi-grounded numeric expressions.  Num-vars
;; is a map from numeric vars introduced to reward directions.  

;; num-fns are functions that restrict a CLP, i.e., partially evalauted 
;; constrain-lp-state-??z functions.

(derive ::SimpleConstraintCondition ::envs/Condition)
(defstruct simple-constraint-condition :class :pos :neg :num-fns :num-vars)

(defn- make-simple-constraint-condition [pos neg num-fns num-vars] 
  (struct simple-constraint-condition ::SimpleConstraintCondition pos neg num-fns num-vars))

(def *true-scc* (make-simple-constraint-condition nil nil nil nil))


;; TODO: figure out how to guess reward direction here
(defn constraint->simple-constraint-condition 
  ([constraint disc-var-map cont-var-map objects const-fns]
     (constraint->simple-constraint-condition constraint disc-var-map cont-var-map objects const-fns {}))
  ([constraint disc-var-map cont-var-map objects const-fns reward-direction-map]
     (let [[pos neg num] (hc/split-constraint constraint disc-var-map objects)]
       (make-simple-constraint-condition
         pos neg 
         (hc/get-fn-yield num disc-var-map cont-var-map const-fns 
                          constrain-lp-state-lez constrain-lp-state-eqz constrain-lp-state-gez)
         (util/map-map #(vector (cont-var-map %) (reward-direction-map %)) (keys cont-var-map))))))

(defmethod envs/conjoin-conditions [::SimpleConstraintCondition ::SimpleConstraintCondition] [c1 c2]
  (update-in    
   (reduce (fn [c1 v] (update-in c1 [v] concat (c2 v))) c1 [:pos :neg :num-fns])
   :num-vars merge (:num-vars c2)))

(defmethod envs/satisfies-condition? ::SimpleConstraintCondition [s c] 
  (throw (UnsupportedOperationException.)))

(defmethod envs/consistent-condition? ::SimpleConstraintCondition [condition] 
  (throw (UnsupportedOperationException.)))


(defmethod restrict-valuation [::HybridDNFLPValuation ::SimpleConstraintCondition] [val condition]
  (let [{:keys [pos neg num-fns num-vars]} condition]
    (make-hybrid-dnf-lp-valuation
     (for [[clause cls] (util/safe-get val :clause-lp-set)
           :let [new-clause 
                 (reduce-while restrict-clause-pos 
                   (reduce-while restrict-clause-neg 
                     clause pos) neg)]
           :when new-clause
           :let [new-cls 
                 (reduce-while #(%2 %1)
                   (reduce (fn [cls [var dir]] (cls/add-lp-state-param cls var [] dir)) cls num-vars)
                   num-fns)]
           :when new-cls]
       [new-clause new-cls]))))





  (set! *warn-on-reflection* false)



(comment 

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
     (fn [[d c] clm strict?] (when-let [nc (constrain-lp-state-gez c clm strict?)] [d nc])))))