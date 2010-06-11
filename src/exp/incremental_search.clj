(ns exp.incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]))


;; Generic incremental search definitions and implementations
; This time captures distinction between *problem* and *solution method*

;Note: possible connection with prolog inference.

;; TODO: fancier info going up
;; TODO: fancier goals, etc. ?

; May need: node merging?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A Summary of a portion of the search space, i.e., descendents of a Node.
; Summary objects should be immutable and Comparable, with "lower" meaning
; "greater upper bound on reward", optionally tiebreaking by other methods.

; Possible: goal criteria: must affect both rewards, solution status, etc.  ?

(defprotocol Summary
  (max-reward [s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A Node is an immutable object describing a portion of a search space, along
; with a single method of decomposing into SubNodes that cover the same portion.

; Note: this essentially mandates that all choices in how to decompose are 
; embedded in the top-level node.  Not sure if this is desirable.

(defprotocol Node
  (node-name [node])
  (solution  [s])  
  (expand    [node]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; IncrementalSearch ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch
  (root-node       [is] "Return the node that is the root of this search.")
  (current-summary [is])
  (next-goal-node  [is min-reward]
     "Evaluate until a goal is found, or the next entry is worse than min-reward (return nil)."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def pos-inf Double/POSITIVE_INFINITY)
(def neg-inf Double/NEGATIVE_INFINITY)

(defmethod queues/get-cost exp.incremental_search.Summary [x] (- (max-reward x)))

(defn viable? [summary min-reward]
  (let [reward (max-reward summary)]
    (and (>= reward min-reward) 
         (> reward neg-inf))))

(defn viable-search? [search min-reward] (viable? (current-summary search) min-reward))

(deftype SimpleSummary [reward]
  Comparable (compareTo  [x] (- (max-reward x) reward))
  Summary    (max-reward       [] reward))

(defn offset-summary [summary reward-offset]
  (SimpleSummary (+ (:reward summary) reward-offset)))

(defn sequence-summaries [s1 s2]
  (SimpleSummary (+ (max-reward s1) (max-reward s2))))

(def worst-summary (SimpleSummary neg-inf))

;(def worst-search
;  (reify IncrementalSearch
;    (root-node       [] (throw (RuntimeException.)))
;    (current-summary [] worst-summary)
;    (next-goal-node  [min-reward] (throw (RuntimeException.)))))



(deftype SimpleNode [name reward solution children data]
  Comparable (compareTo  [x] (- (max-reward x) reward))
  Summary (max-reward [] reward)   
  Node    (node-name  [] name)
          (solution   [] solution)
          (expand     [] children))

(defn make-meta-goal-node [node]
  (SimpleNode (node-name node) (max-reward node) node nil nil))

(defn sequence-goal-nodes [n1 n2]
  (SimpleNode (gensym) (+ (max-reward n1) (max-reward n2)) (into (solution n1) (solution n2)) nil nil))

(defn first-solution-reward-pair [incremental-search]
  (when-let [x (next-goal-node incremental-search neg-inf)]
    [(solution x) (max-reward x)]))

(defn all-goal-nodes [incremental-search]
  (loop [results []]
    (if (not (viable? (current-summary incremental-search) neg-inf)) results
        (recur (util/cons-when (next-goal-node incremental-search neg-inf) results)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Generic Search Implementations ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queue Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defn make-queue [initial-nodes]
;  (doto (queues/make-graph-search-pq) 
;    (queue-add-all!  (cons failed-search initial-nodes))))

(defn pq-add-node  [pq node] (assert (not= :re-added (queues/pq-add! pq (node-name node) node))))
(defn pq-add-nodes [pq nodes] (doseq [node nodes] (pq-add-node pq node)))
(defn pq-summary   [pq] (if (queues/pq-empty? pq) worst-summary (nth (queues/pq-peek-min pq) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat Dijkstra over Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-flat-incremental-dijkstra [root]
  (let [queue (doto (queues/make-graph-search-pq) (pq-add-node root))]
    (reify :as this IncrementalSearch 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (pq-summary queue))
       (next-goal-node  [min-reward]
         (when (viable-search? this min-reward)
           (let [best (nth (queues/pq-remove-min-with-cost! queue) 1)]
;             (println (node-name best))
             (doseq [n (expand best)] (pq-add-node queue n))
             (if (solution best) best (recur min-reward))))))))


;;;;;;;;;;;;;;;;;;;;;;;; Recursive Dijkstra over Searches ;;;;;;;;;;;;;;;;;;;;;;



;; TODO: think about allowing option to expand. 
; Node queue maps node-name --> node.  Search-queue maps [search lift-fn] --> summary.
(defn make-recursive-incremental-dijkstra 
  "Keep graph queue of nodes and tree queue of searches.
   Non-goal nodes are passed to searchify-fn, which should return a [search, ro, lift-fn] pair.
   Goals from searches are passed to corresponding lift-fn, which should return a new node.
     Lift should also work on summaries from this search.
   Never calls expand, *except* on root to get initial nodes. ??
   You could think of the [search, reward-offset, lift-fn] pair as comprising a new type of search, which
   is like an ordinary search but may return nodes that are not goals.
"
  [root searchify-fn]
  (let [search-queue (doto (queues/make-graph-search-pq))
        node-queue   (doto (queues/make-graph-search-pq) (pq-add-nodes (expand root)))
        union-queue  (queues/make-union-pq search-queue node-queue)]
;    (println "MR" root)
    (reify :as this IncrementalSearch 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (pq-summary union-queue))
       (next-goal-node  [min-reward]
;         (println (current-summary this) min-reward)
         (when (viable-search? this min-reward)
           (if (neg? (compare (pq-summary search-queue) (pq-summary node-queue)))
             (let [[[best-search ro lift-fn :as best-pair] summary] 
                     (queues/pq-remove-min-with-cost! search-queue)
                   next-min-reward (max min-reward (max-reward (pq-summary union-queue)))]
               (queues/pq-replace! search-queue best-pair summary) ;; Add back for recursive call
               (when-let [result (next-goal-node best-search (- next-min-reward ro))]
                 (pq-add-node node-queue (lift-fn result)))
               (let [new-summary (current-summary best-search)]
                 (if (viable? new-summary neg-inf)
                   (queues/pq-replace! search-queue best-pair (offset-summary new-summary ro))
                   (queues/pq-remove! search-queue best-pair)))
               (recur min-reward))
             (let [best-node (nth (queues/pq-remove-min-with-cost! node-queue) 1)]
               (if (solution best-node)
                 best-node
                 (let [[search reward-offset lift-fn :as pair] (searchify-fn best-node)]
                   (queues/pq-add! search-queue pair 
                    (offset-summary (current-summary search) reward-offset))
                   (recur min-reward))))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Incremental Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn cache-incremental-search
  "Take a *fresh* incremental-search, and return a function of no arguments that returns 
   independent incremental-search objects backed by it.  Not thread-safe."
  [backing-search]
  (let [results-atom (atom [])
        root         (root-node backing-search)]
    (fn cache-factory []
      (let [index-atom   (atom 0)]
        (reify :as this IncrementalSearch 
         (root-node       [] root)
         (current-summary [] (util/min-comparable (nth @results-atom @index-atom worst-summary) 
                                                  (current-summary backing-search)))
         (next-goal-node  [min-reward]
;           (println (current-summary this) (current-summary backing-search) min-reward)
           (if-let [nxt (nth @results-atom  @index-atom nil)]
             (when (viable? nxt min-reward) (swap! index-atom inc) nxt)
             (when (viable-search? backing-search min-reward)
               (do (when-let [r (next-goal-node backing-search min-reward)] 
                     (swap! results-atom conj r))
                   (recur min-reward))))))))))

(defmacro get-cached-search 
  "Take a Map, name, and expression that constructs a fresh IncrementalSearch.  If this is the first
   call to this function with this name, execute factory-expr, wrap the result in a cache, and return it.
   Subsequent calls with the same name will return a new cached view on the same search, without 
   executing factory-expr."
  [cache-map name factory-expr]
  `((util/cache-with ~cache-map ~name (cache-incremental-search ~factory-expr))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No reason to use this except to emulate SAHTN.
(defn make-eager-search 
  "Fully evaluate the search problem, and return an incremental view on the results.
   Useless except for testing, or to emulate other exhaustive algorithms (e.g., SAHTN)."
  [is]
  (let [c (cache-incremental-search is)]
    (all-goal-nodes (c))
    (c)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sequencing ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sequence two closed searches (with concrete goal states).

(defn make-closed-sequence-search
  "Sequence two searches. Choice-fn takes the searches, and returns the one to refine 
   (only when both non-goal)."
  [root s1 s2 choice-fn]
  (let [s1-goal (atom nil), s2-goal (atom nil)]
    (reify :as this IncrementalSearch 
      (root-node        [] root)      
      (current-summary  [] (sequence-summaries (or @s1-goal (current-summary s1)) 
                                               (or @s2-goal (current-summary s2))))
      (next-goal-node   [min-reward]
        (when (viable-search? this min-reward)
          (let [g1 @s1-goal, g2 @s2-goal]
            (if (and g1 g2)
                (do (reset! s1-goal worst-summary)
                    (sequence-goal-nodes g1 g2))
              (let [choice (cond g1 s2 g2 s1 :else (choice-fn s1 s2))
                    [choice-atom other] (cond (identical? choice s1) [s1-goal s2]
                                              (identical? choice s2) [s2-goal s1])]
                (let [nxt (next-goal-node choice (- min-reward (max-reward other)))]
                  (when nxt (reset! choice-atom nxt))
                  (recur min-reward))))))))))


   



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generalized-Goal Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;??????


