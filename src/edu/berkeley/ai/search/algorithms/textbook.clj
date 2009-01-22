(ns edu.berkeley.ai.search.algorithms.textbook
  (:refer-clojure)
  (:use edu.berkeley.ai.search)
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues] )
  )
  
;;; Textbook algorithms for fully observable, deterministic problems
; with countable state spaces and finite action spaces.
; Does *not* assume positive action costs...

  

(defn depth-first-search         "Tree dfs search"          [node]
  (first-solution node         (queues/make-stack-pq)        (constantly 0)))

(defn depth-first-graph-search   "Graph dfs search"         [node]
  (first-solution node         (queues/make-graph-stack-pq)  (constantly 0)))


(defn breadth-first-search       "Tree bfs search"          [node]
  (first-solution node         (queues/make-queue-pq)        (constantly 0)))

(defn breadth-first-graph-search "Graph bfs search"         [node]
  (first-solution node         (queues/make-graph-queue-pq)  (constantly 0)))


;(defn uniform-cost-search        "Tree uniform-cost search" [node]
;  (first-optimal-solution node (queues/make-tree-search-pq)  #(- (reward-so-far %))))

;(defn uniform-cost-graph-search "Tree uniform-cost search"  [node]
;  (first-optimal-solution node (queues/make-graph-search-pq) #(- (reward-so-far %))))

;(defn stupid-fn [f]
;  #(- (f %)))

(defn a-star-search             "Tree a* search"            [node]
  (first-optimal-solution node (queues/make-tree-search-pq)  (fn negator [x] (- (upper-reward-bound x)))))
;  (first-optimal-solution node (queues/make-tree-search-pq)  #(- (upper-reward-bound %))))


(defn a-star-graph-search       "Graph a* search"           [node]
  (first-optimal-solution node (queues/make-graph-search-pq) #(- (upper-reward-bound %))))



(comment
(time (uniform-cost-search
  (make-search-problem 
   (list 5)
   (let [act-inc (envs/make-action 'inc #(vector (list (inc (first %))) -1))
	 act-dec (envs/make-action 'dec #(vector (list (dec (first %))) -1))] 
     (envs/make-action-space 
      (fn [state]
	(cond (= (first state) 10) [act-dec]
	      (= (first state) 0)  [act-inc]
	      true                 [act-inc act-dec]))))
   (make-goal #(zero? (first %))))))
    
)


  
