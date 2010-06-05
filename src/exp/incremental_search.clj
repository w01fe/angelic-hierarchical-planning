(ns exp.incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues])
  (:import  [java.util HashMap]))


;; Generic incremental search definitions and implementations


;; NOTE: must handle reward decreasses of parital nodes properly. (first versions still mess this up).


;; TODO: fancier info going up
;; TODO: fancier goals, etc. ?

; May need: node merging?
;; TODO: beware of all these reifies, they break equality. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch
  (node-name        [is] "Return the name, used for identity.  Equals and hash-code on object ignored.")
  (goal-state       [is] "Return the goal state of this search, which can be nil meaning 'any new state'")  
  (max-reward       [is] "Upper bound on reward to reach the goal.")
  (optimal-solution [is] "Optimal solution to reach goal-state, or nil if not yet known.")
  (#^IncrementalSearchResult next-results [is min-reward]
     "Evaluate until a goal is found, or the next entry is worse than min-reward.
      Results are typically, but not always, singletons with reward >= min. 
      They are, however, required to be in decreasing order of reward (also across calls)."))

(defn better-search? [s1 s2] (> (max-reward s1) (max-reward s2))) ;; TODO: generify

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def pos-inf Double/POSITIVE_INFINITY)
(def neg-inf Double/NEGATIVE_INFINITY)

(defn viable? [is min-reward]
  (let [reward (max-reward is)]
    (and (>= reward min-reward) 
         (> reward neg-inf))))


(def failed-search
  (reify IncrementalSearch
    (node-name        [] (gensym 'failed))
    (goal-state       [] nil)
    (max-reward       [] neg-inf)
    (optimal-solution [] nil)
    (next-results      [min-reward] (throw (UnsupportedOperationException.)))))

(defn make-goal-search [goal reward solution]
  (reify IncrementalSearch
    (node-name        [] [:goal goal])
    (goal-state       [] goal)
    (max-reward       [] reward)
    (optimal-solution [] solution)
    (next-results      [min-reward] (throw (UnsupportedOperationException.)))))

(defn make-expanding-search [name goal-state init-reward items]
  (let [done?-atom (atom false)]
    (reify IncrementalSearch
      (node-name        [] name)
      (goal-state       [] goal-state)
      (max-reward       [] (if @done?-atom neg-inf init-reward))
      (optimal-solution [] nil)
      (next-results      [min-reward] ;(println "Expand" name init-reward)
        (assert (not @done?-atom)) (reset! done?-atom true)
        items))))

(defn best-search
  ([] failed-search)
  ([s] s) 
  ([s1 s2] (if (better-search? s2 s1) s2 s1)) 
  ([s1 s2 s3 & more] (reduce best-search s1 (cons s2 (cons s3 more)))))


(defn all-results [incremental-search]
  (loop [results []]
    (if (not (viable? incremental-search)) results
        (recur (into results (next-results incremental-search neg-inf))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generic Search Implementations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Incremental Recursive Dijkstra ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wrapper needed since queue expects comparable.

(deftype ComparableSearch [is]
  java.lang.Comparable
   (compareTo [o] (- (max-reward (:is o)) (max-reward is))))

(defmethod queues/get-cost (class (ComparableSearch nil)) [x] (- (max-reward (:is x))))

(defn queue-best [queue]
  (:is (nth (queues/pq-peek-min queue) 1)))

(defn queue-remove-best! [queue]
  (:is (nth (queues/pq-remove-min-with-cost! queue) 1)))

(defn queue-add-all! [queue items]
  (doseq [item items] 
    (util/assert-is (not (= :re-added (queues/g-pq-add! queue (node-name item) (ComparableSearch item))))
                    "%s" [(map node-name items) (println (map node-name items) (map max-reward items))])))

(defn partial-queue-replace! [queue item]
  (if (= (max-reward item) neg-inf)
      (queues/pq-remove! queue (node-name item))   
    (queues/pq-replace! queue (node-name item) (ComparableSearch item))))

(deftype IncrementalDijkstraSearch [name new-queue partial-queue union-queue goal] :as this
  IncrementalSearch
    (node-name        [] name)
    (goal-state       [] goal)
    (max-reward       [] (max-reward (queue-best union-queue))) ;; TODO: too slow - need cache?
    (optimal-solution [] nil)
    (next-results      [min-reward]
      (when (viable? this min-reward)
        (let [best (queue-remove-best! union-queue)]
          (util/print-debug 2 "Best for " name "is " (node-name best) (max-reward best))
          (if (optimal-solution best) [best]
            (let [next-min-reward (max min-reward (max-reward (queue-best union-queue)))]
              (partial-queue-replace! partial-queue best)
              (queue-add-all! new-queue (next-results best next-min-reward))
              (partial-queue-replace! partial-queue best)
              (recur min-reward)))))))


(defn make-queue [initial-nodes]
  (doto (queues/make-graph-search-pq) 
    (queue-add-all!  (cons failed-search initial-nodes))))

(defn make-incremental-dijkstra-search [name initial-nodes goal-state]
  (let [new-q (make-queue initial-nodes) partial-q (queues/make-graph-search-pq)]
;    (println (map max-reward initial-nodes))
;    (println (queues/pq-size new-q) (queues/pq-size partial-q) (max-reward (queue-best new-q)))
    (IncrementalDijkstraSearch name new-q partial-q (queues/make-union-pq new-q partial-q) goal-state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Incremental Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn cache-incremental-search
  "Take a *fresh* incremental-search, and return a function of no arguments that returns 
   independent incremental-search objects backed by it.  Not thread-safe."
  [backing-search]
  (let [results-atom (atom [])
        goal         (goal-state backing-search)
        name         (node-name backing-search)]
    (fn cache-factory []
      (if (optimal-solution backing-search) backing-search
       (let [index-atom   (atom 0)]
         (reify IncrementalSearch
           (node-name        [] name)
           (goal-state       [] goal)
           (optimal-solution [] nil)
           (max-reward       [] (max (max-reward (nth @results-atom @index-atom failed-search)) 
                                     (max-reward backing-search)))
           (next-results [min-reward]
             (if-let [next (nth @results-atom  @index-atom nil)]
               (when (viable? next min-reward) [next])
               (when (viable? backing-search min-reward)
                 (do (swap! results-atom into (next-results backing-search min-reward))
                     (recur min-reward)))))))))))

(defmacro get-cached-search 
  "Take a Map, name, and expression that constructs a fresh IncrementalSearch.  If this is the first
   call to this function with this name, execute factory-expr, wrap the result in a cache, and return it.
   Subsequent calls with the same name will return a new cached view on the same search, without 
   executing factory-expr."
  [cache-map name factory-expr]
  `((util/cache-with ~cache-map ~name (cache-incremental-search ~factory-expr))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No reason to use this except to emulate SAHTN.
;; Note: destroys cost order, but should still work correctly.

(defn make-eager-search 
  "Fully evaluate the search problem, and return an incremental view on the results.
   Useless except for testing, or to emulate other exhaustive algorithms (e.g., SAHTN)."
  [is]
  (let [c (cache-incremental-search is)]
    (all-results (c))
    (c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Transformed Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-transformed-search 
  ([is result-transform] (make-transformed-search is result-transform 0))
  ([is result-transform mro] (make-transformed-search is result-transform mro (goal-state is)))
  ([is result-transform min-reward-offset goal]
     (reify IncrementalSearch
       (goal-state [] goal)
       (next-results [min-reward] (result-transform (next-results is (- min-reward min-reward-offset)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generalized-Goal Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;??????


