(ns angelic.search.action-set.stratified
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [edu.berkeley.ai.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis]
            [angelic.search.action-set.asplan :as asplan]
            )
  (:import [java.util HashSet]))

;; This implements (inefficiently) the stratified planning strategy of 
;; Chen et al. (2009), for comparing # states generated with BI.

(set! *warn-on-reflection* true)

(defn effect-var [a] (util/safe-singleton (keys (:effect-map a))))

(defn stratified-applicable-actions [last-a state tsi actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)]
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (<= b-level a-level)
               (contains? (:precond-map b) a-var))))       
       (actions state)))
    (actions state)))

(defn stratified-search [sas-problem]
  (let [q       (queues/make-tree-search-pq)
        closed  (HashSet.)
        actions (env/actions-fn sas-problem)
        causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        tsi           (graphs/topological-sort-indices causal-graph)
        goal    (env/goal-fn sas-problem)
        init    (env/initial-state sas-problem)]
    (queues/pq-add! q [nil init] 0)
    (println tsi)
    (loop []
      (when-not (queues/pq-empty? q)
        (let [[[last-a state] c] (queues/pq-remove-min-with-cost! q)]
          (util/print-debug 3 "dequeueing " (:act-seq (meta state)) c last-a state "\n")
          (if (goal state)
            [(reverse (:act-seq (meta state))) (:reward (meta state))]
            (do (when-not (.contains closed state)
                  (.add closed state)
                  (doseq [a (stratified-applicable-actions last-a state tsi actions)]
                    (when (env/applicable? a state)
                      (let [[ss sc] (env/successor a state)]
                        (queues/pq-add! q [a ss] (- c sc))))))
                (recur))))))))



;; (use 'angelic.env 'angelic.domains.taxi-infinite 'angelic.domains.sas-problems 'angelic.search.action-set.stratified)

;; (let [e (force (nth ipc2-logistics 3)) ]  (println (time (run-counted #(stratified-search e)))))

;; Logistics results (# states) to match table.
;; 5-2: 19771
;; 6-1: 226446
;; 4-2: 365709
;; 5-1: 677522
;; 4-1: 1030555
;; 4-0: 1281114
;; 6-3: 2747824
;; 6-0: 3435578
;; 6-2: 3286212
;; 5-0: 4053436