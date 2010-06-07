(ns exp.incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues])
  (:import  [java.util HashMap]))


;; Generic incremental search definitions and implementations



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A Summary of a portion of the search space, i.e., descendents of a Node.
; Summary objects should be immutable and Comparable, with "lower" meaning
; "greater upper bound on reward", optionally tiebreaking by other methods.

; Possible: goal criteria: must affect both rewards, solution status, etc.  ?

(defprotocol Summary
  (max-reward [s])
  (solution   [s])
  (is-goal?   [s]))

(defmethod queues/get-cost exp.incremental_search.Summary [x] (- (max-reward x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A Node is an immutable object describing a portion of a search space, along
; with a single method of decomposing into SubNodes that cover the same portion.

; Note: this essentially mandates that all choices in how to decompose are 
; embedded in the top-level node.  Not sure if this is desirable.


(defprotocol Node
  (node-name    [node])
  (expand       [node]))


(deftype SimpleNode [name reward solution children data]
  Comparable (compareTo  [x] (- (max-reward x) reward))
  is/Summary (max-reward [] reward)
             (solution   [] solution)   
  is/Node    (node-name  [] name)
             (expand     [] children))

(defn make-meta-goal-node [node]
  (SimpleNode (node-name node) (max-reward node) node nil nil))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; IncrementalSearch ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch
  (root-node       [is] "Return the node that is the root of this search.")
  (current-summary [is])
  (next-goal-node  [is min-reward]
     "Evaluate until a goal is found, or the next entry is worse than min-reward (return nil).
      Results are typically, but not always, singletons with reward >= min. 
      They are, however, required to be in decreasing order of reward (across calls).
      Searches with a fixed goal should have max-reward infinity after finding first goal."))


; Problem with this is that in recursive searches, we need to transform goal of lower-level
; into something that is not goal of upper-level.  

; (SAHA does not need this faculty).

; Can do this by

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def pos-inf Double/POSITIVE_INFINITY)
(def neg-inf Double/NEGATIVE_INFINITY)

(defn viable? [summary min-reward]
  (let [reward (max-reward summary)]
    (and (>= reward min-reward) 
         (> reward neg-inf))))

(def worst-summary
  (reify Summary
    (max-reward       [] neg-inf)
    (is-goal?         [] false)
    ???
    ))

(def worst-search ...)

(defn all-results [incremental-search]
  (loop [results []]
    (if (not (viable? incremental-search neg-inf)) results
        (recur (into results (next-goal-nodes incremental-search neg-inf))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Generic Search Implementations ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat Dijkstra over Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;

; nodes queued by name

(defn pq-add-node [pq node] (queues/pq-add! (node-name root-node) root-node))

(defn make-flat-incremental-dijkstra [roots]
  (let [queue (doto (queues/make-graph-search-pq) (doseq [root roots] (pq-add-node root)))]
    (reify :as this FlatIncrementalDijkstra 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (nth (queues/pq-peek-min queue) 1))
       (next-goal-node  [min-reward]
         (when (viable? this min-reward)
           (let [best (nth (queues/pq-remove-min-with-cost! queue) 1)]
             (doseq [n (expand best)] (pq-add-node queue n))
             (if (solution best) best (recur min-reward))))))))


;;;;;;;;;;;;;;;;;;;;;;;; Recursive Dijkstra over Searches ;;;;;;;;;;;;;;;;;;;;;;



(deftype RecursiveIncrementalDijkstra [root queue] :as this
  IncrementalSearch
    (root-node       [] root)
    (current-summary [] ???)
    (next-goal-node  [min-reward]
      ...))

(defn make-recursive-incremental-dijkstra 
  "Keep graph queue of nodes and tree queue of searches.
   Non-goal nodes are passed to searchify-fn, which should return a [search, lift-fn] pair.
   Goals from searches are passed to corresponding lift-fn, which should return a new node.
   Never calls expand, so in theory that can be perverted to pass info between lift and searchify."
  [root init-nodes searchify-fn]
  (let [queue (doto (queues/make-graph-search-pq) (pq-add-node root-node))]
    (reify :as this FlatIncrementalDijkstra 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (nth (queues/pq-peek-min queue) 1))
       (next-goal-node  [min-reward]
         (when (viable? this min-reward)
           (let [best (nth (queues/pq-remove-min-with-cost! queue) 1)]
             (doseq [n (expand best)] (pq-add-node queue n))
             (if (solution best) best (recur min-reward))))))))

(defn make-recursive-incremental-dijkstra [root init-node searchify-fn]
  
  
  )



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
;             (println "CACHE" min-reward (max-reward backing-search) (max-reward (nth @results-atom @index-atom failed-search)) @index-atom (count @results-atom))
             (if-let [next (nth @results-atom  @index-atom nil)]
               (when (viable? next min-reward) (swap! index-atom inc) [next])
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
  ([name is result-transform] 
     (make-transformed-search name is result-transform 0))
  ([name is result-transform reward-offset] 
     (make-transformed-search name is result-transform reward-offset (goal-state is)))
  ([name is result-transform reward-offset goal]
     (assert (not (optimal-solution is)))
     (reify IncrementalSearch
       (node-name        [] name)
       (goal-state       [] goal)
       (optimal-solution [] nil)
       (max-reward       [] (+ (max-reward is) reward-offset))
       (next-results [min-reward] 
;         (println "N-R" name min-reward reward-offset) (Thread/sleep 100)
         (map result-transform (next-results is (- min-reward reward-offset)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sequencing ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sequence two closed searches (with concrete goal states).

(defn make-closed-sequence-search
  "Sequence two searches, where goal of s1 must be input of s2.
   Choice-fn takes the searches, and returns the one to refine (only when both non-goal)."
  [name search1 search2 choice-fn]
  (let [s1-atom (atom search1), s2-atom (atom search2) 
        goal    (goal-state search2)]
    (reify :as this IncrementalSearch 
      (node-name        [] name)
      (goal-state       [] goal)
      (optimal-solution [] nil)
      (max-reward       [] (+ (max-reward @s1-atom) (max-reward @s2-atom)))
      (next-results     [min-reward]
        (let [s1 @s1-atom, s2 @s2-atom
              s1-opt (optimal-solution s1) s2-opt (optimal-solution s2)]
          (if (and s1-opt s2-opt)
              (util/prog1 (make-goal-search goal (concat s1-opt s2-opt) (max-reward this))
                          (reset! s1-atom failed-search)) 
            (let [choice (cond s1-opt s2 s2-opt s1 :else (choice-fn s1 s2))
                  [ref-atom oth-atom] (cond (identical? choice s1) [s1-atom s2-atom]
                                            (identical? choice s2) [s2-atom s1-atom]
                                            :else (throw (RuntimeException.)))]
              (let [results (next-results @ref-atom (- min-reward (max-reward @oth-atom)))]
                (assert (<= (count results) 1))
                (when (seq results) 
                  (assert (optimal-solution (first results)))
                  (reset! ref-atom (first results)))
                (when (viable? this min-reward)
                  (recur min-reward))))))))))














;; NOTE: must handle reward decreasses of parital nodes properly. (first versions still mess this up).


;; TODO: fancier info going up
;; TODO: fancier goals, etc. ?

; May need: node merging?
;; TODO: beware of all these reifies, they break equality. 


;; What we're missing here (again)? 
 ;  - distinction between *problem* and *solution method*.
 ;  - Problem has:
 ;     - name
 ;     - (goal-state) -- we shouldn't know anything about this? 
 ;     - max-reward
 ;     - optimal-solution or nil
 ;     - child-subproblems
 ;  - Solution method has:
 ;     - problem
 ;     - next-results [min-reward]
 ;     - (possibly) slurp




; flat / dijkstra solution method:
  ; - dijkstra over problems

; recursive solution method:
  ; - dijkstra over (incremental) searches over problems

; Node can behave directly as a search -- just not incremental.
; Search can behave like a node, as well. ? 


; If we want to support fancier statuses (pessimistic, etc),  want this too.
; Node is its own status.
; Search has separate status. 
; Status includes, at minimum, max-reward.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Really want abstract class ? .. . ?

(defprotocol SearchStatus
  (max-reward       [se]))

(defprotocol SearchEntry
  (name             [se])
  (max-reward       [se])
  (optimal-solution [se]))

(defprotocol SearchNode
  (node-name        [is] "Return the name, used for identity.  Equals and hash-code on object ignored.")
  (node-max-reward  [is] "Upper bound on reward to reach the goal.")
  (optimal-solution [is] "Optimal solution to reach goal-state, or nil if not yet known.")
  (expand           [is] "Return a sequence of sub-nodes, which cover solution space of this one."))

(defprotocol IncrementalSearch
  (root-node        [is] "Return the node that is the root of this search.")
  (is-max-reward    [is] "Current upper bound on reward to reach the goal.")
  (next-goal-nodes  [is min-reward]
     "Evaluate until a goal is found, or the next entry is worse than min-reward.
      Results are typically, but not always, singletons with reward >= min. 
      They are, however, required to be in decreasing order of reward (across calls).
      Searches with a fixed goal should have max-reward infinity after finding first goal."))

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

(deftype ComparableSearch [is max-reward]
  java.lang.Comparable
   (compareTo [o] (- (:max-reward o) max-reward)))

(defn make-comparable-search [is]
  (ComparableSearch is (max-reward is)))

(defmethod queues/get-cost (class (ComparableSearch nil nil)) [x] (- (:max-reward x)))

(defn queue-best [queue]
  (:is (nth (queues/pq-peek-min queue) 1)))

(defn queue-max-reward [queue]
  (:max-reward (nth (queues/pq-peek-min queue) 1)))

(defn queue-remove-best! [queue]
  (:is (nth (queues/pq-remove-min-with-cost! queue) 1)))

(defn queue-add-all! [queue items]
  (doseq [item items] 
    (util/assert-is (not (= :re-added (queues/g-pq-add! queue (node-name item) (make-comparable-search item))))
                    "%s" [(map node-name items) (println (map node-name items) (map max-reward items))])))

(defn partial-queue-replace! [queue item]
  (if (= (max-reward item) neg-inf)
      (queues/pq-remove! queue (node-name item))   
    (queues/pq-replace! queue (node-name item) (make-comparable-search item))))

(deftype IncrementalDijkstraSearch [name new-queue partial-queue union-queue goal] :as this
  IncrementalSearch
    (node-name        [] name)
    (goal-state       [] goal)
    (max-reward       [] (queue-max-reward union-queue)) ;; TODO: too slow - need cache?
    (optimal-solution [] nil)
    (next-results      [min-reward]
      (when (viable? this min-reward)
        (let [;best-rew (queue-max-reward union-queue)
              best (queue-remove-best! union-queue)]
          (util/print-debug 2 "Best for " name "is " (node-name best) (max-reward best) "SZ" (queues/pq-size new-queue) (queues/pq-size partial-queue))
          (if (optimal-solution best) [best]
            (let [next-min-reward (max min-reward (queue-max-reward union-queue))]
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
;             (println "CACHE" min-reward (max-reward backing-search) (max-reward (nth @results-atom @index-atom failed-search)) @index-atom (count @results-atom))
             (if-let [next (nth @results-atom  @index-atom nil)]
               (when (viable? next min-reward) (swap! index-atom inc) [next])
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
  ([name is result-transform] 
     (make-transformed-search name is result-transform 0))
  ([name is result-transform reward-offset] 
     (make-transformed-search name is result-transform reward-offset (goal-state is)))
  ([name is result-transform reward-offset goal]
     (assert (not (optimal-solution is)))
     (reify IncrementalSearch
       (node-name        [] name)
       (goal-state       [] goal)
       (optimal-solution [] nil)
       (max-reward       [] (+ (max-reward is) reward-offset))
       (next-results [min-reward] 
;         (println "N-R" name min-reward reward-offset) (Thread/sleep 100)
         (map result-transform (next-results is (- min-reward reward-offset)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sequencing ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sequence two closed searches (with concrete goal states).

(defn make-closed-sequence-search
  "Sequence two searches, where goal of s1 must be input of s2.
   Choice-fn takes the searches, and returns the one to refine (only when both non-goal)."
  [name search1 search2 choice-fn]
  (let [s1-atom (atom search1), s2-atom (atom search2) 
        goal    (goal-state search2)]
    (reify :as this IncrementalSearch 
      (node-name        [] name)
      (goal-state       [] goal)
      (optimal-solution [] nil)
      (max-reward       [] (+ (max-reward @s1-atom) (max-reward @s2-atom)))
      (next-results     [min-reward]
        (let [s1 @s1-atom, s2 @s2-atom
              s1-opt (optimal-solution s1) s2-opt (optimal-solution s2)]
          (if (and s1-opt s2-opt)
              (util/prog1 (make-goal-search goal (concat s1-opt s2-opt) (max-reward this))
                          (reset! s1-atom failed-search)) 
            (let [choice (cond s1-opt s2 s2-opt s1 :else (choice-fn s1 s2))
                  [ref-atom oth-atom] (cond (identical? choice s1) [s1-atom s2-atom]
                                            (identical? choice s2) [s2-atom s1-atom]
                                            :else (throw (RuntimeException.)))]
              (let [results (next-results @ref-atom (- min-reward (max-reward @oth-atom)))]
                (assert (<= (count results) 1))
                (when (seq results) 
                  (assert (optimal-solution (first results)))
                  (reset! ref-atom (first results)))
                (when (viable? this min-reward)
                  (recur min-reward))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generalized-Goal Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;??????


