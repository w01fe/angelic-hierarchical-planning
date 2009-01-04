; Textbook algorithms for fully observable, deterministic problems
; with countable state spaces and finite action spaces.
; Does *not* assume positive action costs...

(ns edu.berkeley.ai.search.algorithms.textbook
  (:refer-clojure)
  (:use (edu.berkeley.ai [util :as util] search) clojure.contrib.test-is)
  )

(defn depth-first-search         "Tree dfs search"          [node]
  (first-solution node         (make-stack-pq)        (constantly 0)))

(defn depth-first-graph-search   "Graph dfs search"         [node]
  (first-solution node         (make-graph-stack-pq)  (constantly 0)))


(defn breadth-first-search       "Tree bfs search"          [node]
  (first-solution node         (make-queue-pq)        (constantly 0)))

(defn breadth-first-graph-search "Graph bfs search"         [node]
  (first-solution node         (make-graph-queue-pq)  (constantly 0)))


;(defn uniform-cost-search        "Tree uniform-cost search" [node]
;  (first-optimal-solution node (make-tree-search-pq)  #(- (reward-so-far %))))

;(defn uniform-cost-graph-search "Tree uniform-cost search"  [node]
;  (first-optimal-solution node (make-graph-search-pq) #(- (reward-so-far %))))


(defn a-star-search             "Tree a* search"            [node]
  (first-optimal-solution node (make-tree-search-pq)  #(- (upper-reward-bound %))))

(defn a-star-graph-search       "Graph a* search"           [node]
  (first-optimal-solution node (make-graph-search-pq) #(- (upper-reward-bound %))))



(comment
(time (uniform-cost-search
  (make-search-problem 
   (list 5)
   (let [act-inc (make-action 'inc #(vector (list (inc (first %))) -1))
	 act-dec (make-action 'dec #(vector (list (dec (first %))) -1))] 
     (make-action-space 
      (fn [state]
	(cond (= (first state) 10) [act-dec]
	      (= (first state) 0)  [act-inc]
	      true                 [act-inc act-dec]))))
   (make-goal #(zero? (first %))))))

   
     
)


(comment 
(defn depth-first-search "Tree dfs search"
  [search-problem]
  (first-solution (search-problem->state-space-search-state search-problem (constantly Double/NEGATIVE_INFINITY) (constantly Double/POSITIVE_INFINITY))
			  (make-stack-pq) (constantly 0)))
)


(comment 

(declare dfs-)
(defn dfs- [state action-fn goal-test rem-depth] 
  (if (goal-test state) 
      ()
    (some (fn [[action successor cost]]
	    (when-let [result (dfs- successor action-fn goal-test (dec rem-depth))]
	       (cons action result)))
	  (if (zero? rem-depth) nil (successors state action-fn)))))
      

(defn dfs 
  "Standard depth-first search"
  ([search-problem] (dfs search-problem 2000000000))
  ([search-problem depth] 
     (dfs- (:initial-state search-problem) 
	   (:action-fn (:search-space search-problem))
	   (:goal-test search-problem)
	   depth))
  {:test (fn [] (let [action-fn (fn [x] (cond (zero? x) [(make-action 'inc #(vector (inc %) 1))]
						       (= x 10)  [(make-action 'dec #(vector (dec %) 1))]
						       true      [(make-action 'inc #(vector (inc %) 1)) 
								  (make-action 'dec #(vector (dec %) 1))  ]))]
		  (is (nil? (dfs (make-search-problem (make-search-space (range 0 11) [dec inc] action-fn) 5 zero?) 4)) 
		      (= '(inc dec dec dec dec dec dec) 
			 (dfs (make-search-problem (make-search-space (range 0 11) [dec inc] action-fn) 5 zero?) 7)))))}) 

(defn graph-uniform-cost [search-problem]
  "Standard (tree) A* search"
  (let [queue (make-fancy-priority-queue)
	action-fn (:action-fn (:search-space search-problem))
	goal-test (:goal-test search-problem)]
    (fancy-pq-add! queue (:initial-state search-problem) 0)
    (loop []
      (if (fancy-pq-empty? queue) 
	false
	(let [[best cost] (fancy-pq-remove-min-with-cost! queue)]
	  (or (and (goal-test best) cost)
 	      (do (doseq [[action state c2] (successors best action-fn)]
		    (fancy-pq-add! queue state (+ cost c2)))
		  (recur)))))))))
	
  
