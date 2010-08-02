(ns angelic.search.uniform-cost
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [angelic.env :as env]))

;; TODO: tie breaking

(defn uniform-cost-search 
  ([env] (uniform-cost-search env true))
  ([env graph?]
     (let [q (if graph? (queues/make-graph-search-pq) (queues/make-tree-search-pq))
           actions (env/actions-fn env) 
           goal    (env/goal-fn env)]
       (queues/pq-add! q (env/initial-state env) 0)
       (loop []
         (when-not (queues/pq-empty? q)
           (let [[s c] (queues/pq-remove-min-with-cost! q)]
             (util/print-debug 3 "dequeueing " (:act-seq (meta s)) c s "\n")
             (or (and (goal s) [(reverse (:act-seq (meta s))) (:reward (meta s))])
                 (do
                   (let [acts (actions s)]
                     (util/print-debug 4 "Actions are:" acts "\n")
                     (doseq [a acts :when (env/applicable? a s)]
                       (let [[ss sc] (env/successor a s)]
                         (queues/pq-add! q ss (- c sc)))))
                   (recur)))))))))



