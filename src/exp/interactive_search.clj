(ns exp.interactive-search
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues] 
            [exp [hierarchical-incremental-search :as his] [hierarchy :as hierarchy] [env :as env]]
            ))


(def *n)
(def *nn)
(def *ns)
(defn interactive-search 
  ([root reward-fn expand-fn goal-fn] 
     (interactive-search root reward-fn expand-fn goal-fn identity))
  ([root reward-fn expand-fn goal-fn pretty-node-fn]
     (interactive-search root reward-fn expand-fn goal-fn pretty-node-fn (queues/make-graph-search-pq)) )
  ([root reward-fn expand-fn goal-fn pretty-node-fn pq]
     (queues/pq-add! pq root (- (reward-fn root)))
     (let [n-skip (util/sref 0)]
       (loop []
         (when-not (queues/pq-empty? pq)
           (let [[next p] (queues/pq-remove-min-with-cost! pq)
                 goal?    (goal-fn next)
                 refs     (when-not goal? (expand-fn next))
                 dead-end? (and (not goal?) (empty? refs))]
             (print "\n\n" (pretty-node-fn next) (reward-fn next))
             (cond dead-end?     (print " is a dead end.")
                   goal?         (print " is a solution.")
                   :else (print " has successors \n                    " 
                           (util/str-join "\n  " (map (juxt pretty-node-fn reward-fn) refs)) "\n"))
             (or (and goal? next)
                 (when (or (when (> (util/sref-get n-skip) 0)
                             (util/sref-up! n-skip dec)
                             (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs))
                             true)
                           (loop []
                             (print "\n(d)rop, (n)ext, (s)ave, (q)uit, (r)eroot, go (#), (expr ... *n/*nn/*ns)? ")
                             (flush)
                             (let [result (read)]
                               (cond (= result 'd) true
                                     (= result 'n) (do (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs)) true)
                                     (= result 'r) (do (while (not (queues/pq-empty? pq)) (queues/pq-remove-min! pq))
                                                       (queues/pq-replace! pq next (- (reward-fn next)))
                                                       true)
                                     (= result 's) (do (def *n next) (recur))
                                     (= result 'q) false
                                     (integer? result) (do (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs))
                                                           (util/sref-set! n-skip (dec result))
                                                           true)
                                     :else          (do (print (binding [*n next *nn (first refs)
                                                                         *ns (concat refs (map first (queues/pq-peek-pairs pq)))] 
                                                                 (eval result)) "\n") (recur))))))
                   (recur)))))))))

(defn interactive-hierarchical-search [henv]
  (let [e    (hierarchy/env henv)
;        init (env/initial-logging-state e)
        tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])]
    (interactive-search 
     (his/make-root-hfs (env/initial-state e) tla)
     :reward
     his/hfs-children
     #(empty? (:remaining-actions %))
     his/hfs-name)))