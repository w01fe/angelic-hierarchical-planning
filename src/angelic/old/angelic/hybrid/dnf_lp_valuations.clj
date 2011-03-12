;; This file defines valuations for hybrid problems, where we consider sets of 
;; (discrete dnf clause, continuous-lp-state) pairs.  

;; A corresponding kind of description, corresponding to a primitive, discrete-grounded
;; but continuous-ungrounded hybrid strips action, is also defined.


(ns angelic.old.angelic.hybrid.dnf-lp-valuations
  (:use clojure.test angelic.old.angelic
	[angelic.util :as util] [angelic.old  [envs :as envs]]
	[angelic.util [propositions :as props] [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]
	[angelic.old.envs.hybrid-strips :as hs]
	[angelic.old.envs.hybrid-strips [constraints :as hc] [effects :as he]]
	[angelic.old.angelic.hybrid [continuous-lp-states :as cls]]))

(set! *warn-on-reflection* true)



(derive ::HybridDNFLPValuation :angelic.old.angelic/Valuation)

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
	(make-lp-state cont true rew)]))))

(defmethod explicit-valuation-map ::HybridDNFLPValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation-max-reward ::HybridDNFLPValuation [val]
  (apply max 
   Double/NEGATIVE_INFINITY
   (util/map-when #(last (cls/solve-lp-state (second %))) (:clause-lp-set val))))

(defmethod empty-valuation? ::HybridDNFLPValuation [val] false)

(defmethod valuation->pred-maps ::HybridDNFLPValuation valuation->pred-maps-dnf [val]
  (map #(clause->pred-maps (first %)) (:clause-lp-set val)))

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

;(defn translate-simple-constraint-condition [scc trans-disc-var-map]
;  (assert (= (:class scc) ::SimpleConstraintCondition))
;  (reduce (fn [scc key]
;            (update-in scc [key] #(for [atom %] (props/simplify-atom trans-disc-var-map atom))))
;          scc [:pos :neg]))

(defmethod envs/conjoin-conditions [::SimpleConstraintCondition ::SimpleConstraintCondition] [c1 c2]
  (update-in    
   (reduce (fn [c1 v] (update-in c1 [v] concat (c2 v))) c1 [:pos :neg :num-fns])
   [:num-vars] merge (:num-vars c2)))

(defmethod envs/satisfies-condition? ::SimpleConstraintCondition [s c] 
  (throw (UnsupportedOperationException.)))

;; TODO: is it okay to err this way?  
(defmethod envs/consistent-condition? ::SimpleConstraintCondition [condition]
  (empty? (util/intersection-coll (util/to-set (:pos condition)) (:neg condition)))
;  (throw (UnsupportedOperationException.))
  )


(defmethod restrict-valuation [::HybridDNFLPValuation ::SimpleConstraintCondition] [val condition]
  (let [{:keys [pos neg num-fns num-vars]} condition]
    (make-hybrid-dnf-lp-valuation
     (for [[clause cls] (util/safe-get val :clause-lp-set)
           :let [new-clause 
                 (reduce-while restrict-clause-pos 
                   (reduce-while restrict-clause-neg clause neg) 
                   pos)]
           :when new-clause
           :let [new-cls 
                 (reduce-while #(%2 %1)
                   (reduce (fn [cls [var dir]] (cls/add-lp-state-param cls var [] dir)) cls num-vars)
                   num-fns)]
           :when new-cls]
       [new-clause new-cls]))))







  (set! *warn-on-reflection* false)


(comment 

  ;; Commands for looking at proliferation of valuation sizes
  
(count (:clause-lp-set (optimistic-valuation (:previous (:previous (:plan *n))))))

(doseq [a (rest (reverse (iterate-while :previous (:previous (:previous (:plan *n))))))] (println (hla-name (:hla a)) (count (:clause-lp-set (optimistic-valuation a)))))
)