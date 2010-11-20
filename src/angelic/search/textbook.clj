(ns angelic.search.textbook
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [angelic.env :as env]))

;; TODO: tie breaking

(defn a*-search
  ([env heuristic] (a*-search env heuristic true))
  ([env heuristic graph?]
     (let [q (if graph? (queues/make-graph-search-pq) (queues/make-tree-search-pq))
           actions (env/actions-fn env) 
           goal    (env/goal-fn env)
           init    (env/initial-state env)]
       (queues/pq-add! q init (heuristic init))
       (loop []
         (when-not (queues/pq-empty? q)
           (let [[s c] (queues/pq-remove-min-with-cost! q)]
             (util/print-debug 3 "dequeueing " (:act-seq (meta s)) c s "\n")
             (or (and (goal s) [(reverse (:act-seq (meta s))) (:reward (meta s)) #_ (println s)])
                 (do
                   (let [acts (actions s)]
                     (util/print-debug 4 "Actions are:" (map env/action-name acts) "\n")
                     (doseq [a acts :when (env/applicable? a s)]
                       (let [[ss sc] (env/successor a s)
                             f-val (+ (:reward (meta ss)) (heuristic ss))]
                         (when (> f-val Double/NEGATIVE_INFINITY)
                           (util/print-debug 1 "warning: pruning " ss)
                           (queues/pq-add! q ss (- 0 f-val ))))))
                   (recur)))))))))


(defn uniform-cost-search
  ([env] (uniform-cost-search env true))
  ([env graph?] (a*-search env (constantly 0) graph?)))


