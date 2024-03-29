(ns angelic.search.interactive
  (:require [angelic.util :as util]
            [angelic.util.queues :as queues]
            [angelic.env :as env]
            [angelic.hierarchy :as hierarchy]))


(def *n)
(def *nn)
(def *ns)
(defn generic-interactive-search 
  ([root reward-fn expand-fn goal-fn] 
     (generic-interactive-search root reward-fn expand-fn goal-fn identity))
  ([root reward-fn expand-fn goal-fn pretty-node-fn]
     (generic-interactive-search root reward-fn expand-fn goal-fn pretty-node-fn (queues/make-graph-search-pq)) )
  ([root reward-fn expand-fn goal-fn pretty-node-fn pq]
     (queues/pq-add! pq root (- (reward-fn root)))
     (let [n-skip (util/sref 0)
           ff?    (util/sref false)]
       (loop []
         (when-not (queues/pq-empty? pq)
           (let [[nxt p] (queues/pq-remove-min-with-cost! pq)
                 next     (if (util/sref-get ff?) 
                              (loop [n nxt] (if (goal-fn n) n (let [r (expand-fn n)] (if-let [s (util/singleton r)] (recur s) n))))
                            nxt)
                 goal?    (goal-fn next)
                 refs     (when-not goal? (expand-fn next))
                 dead-end? (and (not goal?) (empty? refs))]
             (util/sref-set! ff? false)
             (print "\n\n" (pretty-node-fn nxt) (reward-fn nxt))
             (cond dead-end?     (print " leads to dead end at:\n" (pretty-node-fn next) (reward-fn next) )
                   goal?         (print " leads to solution:\n" (pretty-node-fn next) (reward-fn next) )
                   :else (print " has successors \n                    " 
                           (util/str-join "\n  " (map (juxt pretty-node-fn reward-fn) refs)) "\n"))
             (or (and goal? next)
                 (when (or (when (> (util/sref-get n-skip) 0)
                             (util/sref-up! n-skip dec)
                             (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs))
                             true)
                           (loop []
                             (print "\n(n)ext, (f)ast forward, (d)rop, (s)ave, (q)uit, (r)eroot, go (#), (expr ... *n/*nn/*ns)? ")
                             (flush)
                             (let [result (read)]
                               (cond (= result 'd) true
                                     (= result 'f) (do (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs)) (util/sref-set! ff? true) true)
                                     (= result 'n) (do (queues/pq-add-all! pq (map (fn [i] [i (- (reward-fn i))]) refs)) true)                                                                   (= result 'r) (do (while (not (queues/pq-empty? pq)) (queues/pq-remove-min! pq))
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

(defn interactive-search [env]
  (generic-interactive-search 
   (with-meta  (env/initial-state env) {:reward 0})
   #(:reward (meta %)) 
   (let [a-fn (env/actions-fn env)]
     #(for [a (a-fn %) :when (env/applicable? a %)] (first (env/successor a %))))
   (env/goal-fn env)
   #(:act-seq (meta %))))

