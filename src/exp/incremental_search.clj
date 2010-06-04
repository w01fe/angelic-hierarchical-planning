(ns exp.incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues])
  (:import  [java.util HashMap]))


;; Generic incremental dijkstra algorithm


;; NOTE: must handle reward decreasses of parital nodes properly. (first versions still mess this up).


;; TODO: fancier info going up
;; TODO: fancier goals, etc.
;; TODO: tests
;; TODO: merge searches and nodes
;; TODO: more general ways to express sequencing, primitives?

; May need: node merging?

; Question: What does search return?
;  Can return [updated GoalInfo, new GoalInfos]
;  Should be able to return new searches too, though; how does that fit in?
;   This is really similar to new outcome states.  Just not associated with *this* search.
;   Whatever, should not be too inefficient for transparent case either. 
; Question: is every parent set up to handle both kinds of new things?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assume "nil" is special state, meaning "everything else".

(defprotocol IncrementalSearchStatus
  (max-reward       [gi] "Upper bound on reward to reach this goal.")
  (optimal-solution [gi] "Optimal solution to reach goal-state, or nil if not yet known."))

(defmethod queues/get-cost IncrementalSearchStatus [gi] (- (max-reward gi)))

;; TODO: generify
(defn better-status? [s1 s2] (> (max-reward s1) (max-reward s2)))


(deftype IncrementalSearchResult [new-status new-search-status-pairs])

(defprotocol IncrementalSearch 
  (goal-state                            [is])
  (#^IncrementalSearchResult next-result [is min-reward]
     "Stopping-fn is a function from next status to boolean, telling us whether to stop before
      expanding that node.  We may stop earlier for other reasons, based on type of search.
      Returns an IncrementalSearchResult; all statusus must have max-reward <= that of this."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def pos-inf Double/POSITIVE_INFINITY)
(def neg-inf Double/NEGATIVE_INFINITY)

(defn viable? [status min-reward]
  (let [reward (max-reward status)]
    (and (>= reward min-reward) 
         (> reward neg-inf))))


(def *best-status*
  (reify IncrementalSearchStatus
    (max-reward [] pos-inf)
    (optimal-solution [] nil)))

(def *worst-status*
  (reify IncrementalSearchStatus
    (max-reward [] neg-inf)
    (optimal-solution [] nil)))

(def *worst-search*
  (let [worst-result (IncrementalSearchResult *worst-status* [])]
    (reify IncrementalSearch
      (goal-state  [] nil)
      (next-result [min-reward] worst-result))))

(def *worst-ss-pair* [*worst-status* *worst-search*])


(defn best-status 
  ([] *worst-status*)
  ([s] s) 
  ([s1 s2] (if (better-status? s2 s1) s2 s1)) 
  ([s1 s2 s3 & more] (reduce best-status s1 (cons s2 (cons s3 more)))))


(defn all-results [incremental-search]
  (loop [status *best-status* results []]
    (if (not (viable? status neg-inf)) results
      (let [{:keys [new-status new-search-status-pairs]} (next-result incremental-search neg-inf)]
        (recur new-status (into results new-search-status-pairs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generic Search Implementations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Incremental Recursive Dijkstra ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn queue-best-status [queue]
  (nth (queues/pq-peek-min queue) 1))

(defn incremental-dijkstra-step 
  "Expand queue items until (1) goal, or (2) best max-reward falls below min-reward. 
   Returns an IncrementalSearchResult.  Safe against recursive calls through next-result."
  [new-queue partial-queue goal-fn min-reward]
  (let [queue (queues/make-union-pq new-queue partial-queue)]
    (loop []
      (or (let [best-status (queue-best-status queue)] 
            (when (viable? best-status min-reward) 
              (IncrementalSearchResult best-status nil))) 
          (let [[best best-status] (queues/pq-remove-min-with-cost! queue)]
            (or (when-let [g (goal-fn best best-status)] 
                  (IncrementalSearchResult (queue-best-status queue) [[best best-status]]))
                (let [next-min-reward (max min-reward (max-reward (queue-best-status queue)))]
                  (queues/pq-replace! partial-queue best best-status)
                  (let [{:keys [new-status new-search-status-pairs]} (next-result best next-min-reward)]
                    (if (= (max-reward new-status) neg-inf) 
                        (queues/pq-remove! partial-queue best)
                      (queues/pq-replace! partial-queue best new-status))
                    (doseq [[s ss] new-search-status-pairs] 
                      (assert (not (= :re-added (queues/pq-add! new-queue s ss)))))
                    (recur)))))))))

(defn make-queue [initial-elements]
  (doto (queues/make-graph-search-pq)
    (queues/pq-add! *worst-search* *worst-status*)
    (queues/pq-add-all! initial-elements)))

(defn make-incremental-dijkstra-search [initial-pairs goal-state]
  (let [new-q (make-queue initial-pairs) partial-q (make-queue nil)]
    (reify IncrementalSearch
      (goal-state [] goal-state)
      (next-result [min-reward] 
        (incremental-dijkstra-step new-q partial-q optimal-solution min-reward)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Incremental Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn cache-incremental-search
  "Take a *fresh* incremental-search, and return a function of no arguments that returns 
   independent incremental-search objects backed by it.  Not thread-safe."
  [backing-search]
  (let [result-pair-atom (atom [])
        next-status-atom *best-status*
        b-goal-state     (goal-state backing-search)]
    (fn cache-factory []
      (let [index-atom   (atom 0)]
        (reify IncrementalSearch
          (goal-state [] b-goal-state)
          (next-result [min-reward]
            (let [result-pairs @result-pair-atom]
              (if-let [[_ next-status :as result] (nth result-pairs @index-atom nil)]
                (if (viable? next-status min-reward) ; New result in range
                    (IncrementalSearchResult 
                     (best-status @next-status-atom (nth (get result-pairs (swap! index-atom inc) 
                                                              *worst-ss-pair*) 1))
                     [result]) 
                  (IncrementalSearchResult next-status nil))
                (if (viable? @next-status-atom min-reward)
                  (let [{:keys [new-status new-search-status-pairs]} (next-result backing-search min-reward)]
                    (reset! next-status-atom new-status)
                    (swap!  result-pair-atom into new-search-status-pairs)
                    (recur min-reward))
                  (IncrementalSearchResult @next-status-atom nil))))))))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




