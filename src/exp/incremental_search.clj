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

; A Node is an immutable object naming a portion of a search space, 
; We never try to expand or search past a goal node.  Make 2 nodes if you want this.

(defprotocol Node
  (node-name  [node])
  (node-goal? [node]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; IncrementalSearch ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch
  (root-node       [is] "Return the node that is the root of this search.")
  (current-summary [is])
  (next-goal       [is min-reward]
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

(defn offset-simple-summary [summary reward-offset]
  (SimpleSummary (+ (:reward summary) reward-offset)))

(defn add-simple-summaries [s1 s2]
  (SimpleSummary (+ (max-reward s1) (max-reward s2))))

(def worst-simple-summary (SimpleSummary neg-inf))


(deftype SimpleNode [name reward goal? data]
  Comparable (compareTo  [x] 
               (let [c  (- (max-reward x) reward)]
                 (if (not (zero? c)) c
                   (cond goal? -1 
                         (and (instance? exp.incremental_search.Node x) (node-goal? x)) 1
                         :else 0))))
  Summary (max-reward [] reward)   
  Node    (node-name  [] name)
          (node-goal? [] goal?))

(defn name-str [x]
  (let [n (:name x)]
    (if (symbol? n) n
        (vec (map #(if (instance? exp.env.FactoredState %) (dissoc (exp.env/as-map %) :const) %) n)))))

(defmethod print-method ::SimpleNode [x s]
  (print-method (str "Nd<" (name-str x) "," (:reward x) "," (:goal? x) ">") s))


(defn first-goal-node [incremental-search] (next-goal incremental-search neg-inf))

(defn all-goal-nodes [incremental-search]
  (loop [results []]
    (if (not (viable? (current-summary incremental-search) neg-inf)) results
        (recur (util/cons-when (next-goal incremental-search neg-inf) results)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Generic Search Implementations ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queue Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn pq-add-node  [pq node] (assert (not= :re-added (queues/pq-add! pq (node-name node) node))))
(defn pq-add-nodes [pq nodes] (doseq [node nodes] (pq-add-node pq node)))
(defn pq-summary   [pq] (if (queues/pq-empty? pq) worst-summary (nth (queues/pq-peek-min pq) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat Dijkstra over Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-flat-incremental-dijkstra [root expand-fn]
  (let [queue (doto (queues/make-graph-search-pq) (pq-add-node root))]
    (reify :as this IncrementalSearch 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (pq-summary queue))
       (next-goal  [min-reward]
         (when (viable-search? this min-reward)
           (let [best (nth (queues/pq-remove-min-with-cost! queue) 1)]             
             (if (node-goal? best) 
                 best 
               (do (doseq [n (expand-fn best)] (pq-add-node queue n)) (recur min-reward)))))))))


;;;;;;;;;;;;;;;;;;;;;;;; Recursive Dijkstra over Searches ;;;;;;;;;;;;;;;;;;;;;;

; TODO: think about reducing overhead of hashing searches.

(defprotocol SubSearch
  (sub-current-summary [ss])
  (sub-next-node       [ss min-reward]))

(extend exp.incremental_search.IncrementalSearch
   SubSearch #{:sub-current-summary sub-current-summary :next-goal sub-next-node})

(deftype WrappedSubSearch [search reward-offset summary-lift-fn goal-lift-fn]
  SubSearch (sub-current-summary [] (summary-lift-fn (current-summary search)))
            (sub-next-node [min-reward] 
              (util/aand (next-goal search (- min-reward reward-offset)) (goal-lift-fn it))))


; Node queue maps node-name --> node.  Search-queue maps [search lift-fn] --> summary.
(defn make-recursive-incremental-dijkstra 
  "Keep graph queue of nodes and tree queue of searches.
   Non-goal nodes are passed to searchify-fn, which should return a 
     SubgoalSearch (or list of nodes, to shortcut.)"
  [root searchify-fn]
  (let [search-queue (doto (queues/make-graph-search-pq))
        node-queue   (doto (queues/make-graph-search-pq) (pq-add-node root))
        union-queue  (queues/make-union-pq search-queue node-queue)]
    (reify :as this IncrementalSearch 
      IncrementalSearch
       (root-node       [] root)
       (current-summary [] (pq-summary union-queue))
       (next-goal  [min-reward]
;         (println "\n Ref-rec" root (max-reward (current-summary this)) min-reward) (Thread/sleep 100)
         (when (viable-search? this min-reward)
           (if (neg? (compare (pq-summary search-queue) (pq-summary node-queue)))
             (let [[best-sgs summary] (queues/pq-remove-min-with-cost! search-queue)
                   next-min-reward    (max min-reward (max-reward (pq-summary union-queue)))]
               (queues/pq-replace! search-queue best-sgs summary) ;; Add back for recursive call
               (when-let [result (sub-next-node best-sgs min-reward)]
                 (pq-add-node node-queue result))
               (let [new-summary (sub-current-summary best-sgs)]
                 (if (viable? new-summary neg-inf)
                   (queues/pq-replace! search-queue best-sgs new-summary)
                   (queues/pq-remove! search-queue best-sgs)))
               (recur min-reward))
             (let [best-node (nth (queues/pq-remove-min-with-cost! node-queue) 1)]
               (if (node-goal? best-node)
                 best-node
                 (let [sgs-or-nodes (searchify-fn best-node)]
                   (if (coll? sgs-or-nodes) 
                     (pq-add-nodes node-queue sgs-or-nodes)
                     (queues/pq-add! search-queue sgs-or-nodes (sub-current-summary sgs-or-nodes)))
                   (recur min-reward))))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Incremental Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn cache-incremental-search
  "Take a *fresh* incremental-search, and return a function of no arguments that returns 
   independent incremental-search objects backed by it.  Not thread-safe."
  [backing-search]
  (let [results-atom (atom [])]
    (fn cache-factory []
      (let [root         (root-node backing-search)
            index-atom   (atom 0)]
        (reify :as this IncrementalSearch 
         (root-node       [] root)
         (current-summary [] (util/min-comparable (nth @results-atom @index-atom worst-summary) 
                                                  (current-summary backing-search)))
         (next-goal  [min-reward]
;           (println (current-summary this) (current-summary backing-search) min-reward)
           (if-let [nxt (nth @results-atom  @index-atom nil)]
             (when (viable? nxt min-reward) (swap! index-atom inc) nxt)
             (when (viable-search? backing-search min-reward)
               (do (when-let [r (next-goal backing-search min-reward)] 
                     (swap! results-atom conj r))
                   (recur min-reward))))))))))

(defmacro get-cached-search 
  "Take a Map, name, and expression that constructs a fresh IncrementalSearch.  If this is the first
   call to this function with this name, execute factory-expr, wrap the result in a cache, and return it.
   Subsequent calls with the same name will return a new cached view on the same search, without 
   executing factory-expr."
  [cache-map name factory-expr]
  `((util/cache-with ~cache-map ~name (cache-incremental-search ~factory-expr))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Goal-Filtered Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This allows a single forward saerch to be shared in contexts with same start but different
; goals. Like cached search, but indexes results by goal values.

(defn generalize-incremental-search
  [backing-search goal-val-fn]
  (let [results-atom (atom {})]
    (fn cache-factory [goal-val]
      (let [root         (root-node backing-search)
            index-atom   (atom 0)]
        (reify :as this IncrementalSearch 
         (root-node       [] root)
         (current-summary [] (util/min-comparable (get-in @results-atom [goal-val @index-atom] worst-summary) 
                                                  (current-summary backing-search)))
         (next-goal  [min-reward]
           (if-let [nxt (get-in @results-atom [goal-val @index-atom] nil)]
             (when (viable? nxt min-reward) (swap! index-atom inc) nxt)
             (when (viable-search? backing-search min-reward)
               (do (when-let [r (next-goal backing-search min-reward)] 
                     (swap! results-atom update-in [(goal-val-fn r)] #(conj (or % []) r)))
                   (recur min-reward))))))))))

(defmacro get-generalized-search
  "Take a Map, name, and expression that constructs a fresh IncrementalSearch.  If this is the first
   call to this function with this name, execute factory-expr, wrap the result in a cache, and return it.
   Subsequent calls with the same name will return a new cached view on the same search, without 
   executing factory-expr."
  [cache-map name goal-val-fn goal-val factory-expr]
  `((util/cache-with ~cache-map ~name (generalize-incremental-search ~factory-expr ~goal-val-fn)) ~goal-val))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No reason to use this except to emulate SAHTN.
(defn make-eager-search 
  "Fully evaluate the search problem, and return an incremental view on the results.
   Useless except for testing, or to emulate other exhaustive algorithms (e.g., SAHTN)."
  [is]
  (let [c (cache-incremental-search is)]
    (all-goal-nodes (c))
    (c)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Delayed Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-delayed-search
  "Report back the given summary at first, then delegate to provided search thereafter."
  [root init-summary backing-search]
  (let [a (atom init-summary)]
    (reify :as this IncrementalSearch
           (root-node [] root)
           (current-summary [] @a)
           (next-goal [min-reward] 
                           (let [b-s (force backing-search)
                                 result (next-goal b-s min-reward)]
                             (reset! a (current-summary b-s))
                             result)))))
; Delayed search reports back 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sequencing ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sequence two closed searches (with concrete goal states).

(defn make-and-search
  "Sequence two searches. Choice-fn takes the searches, and returns the one to refine 
   (only when both non-goal). other fns tell how to combine summaries and goals."
  [root s1 s2 choice-fn and-summary-fn and-goal-fn]
  (let [s1-goal (atom nil), s2-goal (atom nil)]
    (reify :as this IncrementalSearch 
      (root-node        [] root)      
      (current-summary  [] (and-summary-fn (or @s1-goal (current-summary s1)) 
                                           (or @s2-goal (current-summary s2))))
      (next-goal   [min-reward]
;        (println "\n Seq-rec" root (max-reward (current-summary this)) min-reward) (Thread/sleep 100)
        (when (viable-search? this min-reward)
          (let [g1 @s1-goal, g2 @s2-goal]
            (if (and g1 g2)
                (do (reset! s1-goal worst-summary)
                    (and-goal-fn g1 g2))
              (let [choice (cond g1 s2 g2 s1 :else (choice-fn s1 s2))
                    [choice-atom other-sum] 
                      (cond (identical? choice s1) [s1-goal (or @s2-goal (current-summary s2))]
                            (identical? choice s2) [s2-goal (or @s1-goal (current-summary s1))])]
                (let [nxt (next-goal choice (- min-reward (max-reward other-sum)))]
                  (when nxt (reset! choice-atom nxt))
                  (recur min-reward))))))))))


   



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generalized-Goal Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;??????


