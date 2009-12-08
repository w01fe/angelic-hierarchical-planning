(ns exp.ucs
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env]]))

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
             (or (goal s)
                 (do
                   (doseq [a (actions s) :when (env/applicable? a s)]
                     (let [[ss sc] (env/successor a s)]
                       (queues/pq-add! q ss (- c sc))))
                   (recur)))))))))

;; Two other algorithms: exhaustive HTN, and SA-HTN, possibly also SA-HTN-queue.
; Issues of DP in standard search.  


