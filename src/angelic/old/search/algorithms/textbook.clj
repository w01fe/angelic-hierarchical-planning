(ns angelic.old.search.algorithms.textbook
  (:refer-clojure)
  (:use angelic.old.search)
  (:require [angelic.util :as util] [angelic.util.queues :as queues] )
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

(defn uniform-cost-graph-search "Tree uniform-cost search"  [node]
  (first-optimal-solution node (queues/make-graph-search-pq) #(- (reward-so-far %))))

(defn a-star-priority-fn [x] ;(util/prln 
  [(- (upper-reward-bound x))
   (- (node-depth x))])


(defn a-star-search             "Tree a* search"            [node]
  (first-optimal-solution node (queues/make-tree-search-pq)  a-star-priority-fn #_(fn negator [x] (- (upper-reward-bound x)))))

(defn a-star-graph-search       "Graph a* search"           [node]
  (first-optimal-solution node (queues/make-graph-search-pq) a-star-priority-fn #_ (fn negator [x] (- (upper-reward-bound x)))))


(defn get-weighted-a-star-priority-fn [wt]
    (fn was [x] (- (* (dec wt) (reward-so-far x)) (* wt (upper-reward-bound x)))))
  

(defn weighted-a-star-search    "Tree wtd a* search"        [node wt]
  (first-optimal-solution node (queues/make-tree-search-pq) (get-weighted-a-star-priority-fn wt))) 

(defn weighted-a-star-graph-search  "Graph wtd a* search"   [node wt]
  (first-optimal-solution node (queues/make-graph-search-pq)(get-weighted-a-star-priority-fn wt)))



;; Optimistic A* tree search ( simplified version of Thayer+Ruml, ICAPS 08)


(defn- add-to-queues! [prim-pq prim-pf sec-pq sec-pf item]
    (queues/pq-add! prim-pq item (prim-pf item))
    (queues/pq-add! sec-pq item (sec-pf item)))

(defn- remove-min-from-queues! [prim-pq sec-pq]
  (let [item (queues/pq-remove-min! prim-pq)]
    (queues/pq-remove! sec-pq item)
    item))

(defn optimistic-a-star-search 
  "Simplified Optimistic A* (Thayer+Ruml, ICAPS08)" 
  [node wt sub-pf]
  (let [opt-pf (fn negator [x] (- (upper-reward-bound x)))
	opt-pq (queues/make-fancy-tree-search-pq)
	sub-pq (queues/make-fancy-tree-search-pq)]
    (add-to-queues! opt-pq opt-pf sub-pq sub-pf node)
    (loop [sol nil, sol-cost (+ 0 Double/POSITIVE_INFINITY)]
      (cond (queues/pq-empty? opt-pq)   
              (do (util/assert-is (= sol-cost Double/POSITIVE_INFINITY)) nil)
	    (>= (* wt (second (queues/pq-peek-min opt-pq))) sol-cost)
	      [sol (- sol-cost)]
	    :else
	(let [n (if (< (second (queues/pq-peek-min sub-pq)) sol-cost)
		    (remove-min-from-queues! sub-pq opt-pq)
		  (remove-min-from-queues! opt-pq sub-pq))
	      n-sol (extract-optimal-solution n)]
	  (doseq [c (immediate-refinements n)]
;	      (println (node-str n) (node-str c) (opt-pf c) (sub-pf c))
	    (add-to-queues! opt-pq opt-pf sub-pq sub-pf c))
	  (if (and n-sol (< (- (second n-sol)) sol-cost))
	      (do (util/assert-is (= (second n-sol) (upper-reward-bound n)))
		  (util/assert-is (= (second n-sol) (sub-pf n)))
		  (recur (first n-sol) (- (second n-sol))))
	    (recur sol sol-cost)))))))



;; Optimistic A* tree search ( almost paper version of Thayer+Ruml, ICAPS 08)

(defn- add-to-graph-queues! [prim-pq prim-pf sec-pq sec-pf item]
  (when-not (= :ignored (queues/pq-add! prim-pq item (prim-pf item)))
    (queues/pq-replace! sec-pq item (sec-pf item))))

(defn optimistic-a-star-graph-search 
  "Optimistic A* (Thayer+Ruml, ICAPS08)" 
  [node wt sub-pf]
  (let [opt-pf (fn negator [x] (- (upper-reward-bound x)))
	opt-pq (queues/make-graph-search-pq)
	sub-pq (queues/make-graph-search-pq)]
    (add-to-graph-queues! opt-pq opt-pf sub-pq sub-pf node)
    (loop [sol nil, sol-cost (+ 0 Double/POSITIVE_INFINITY)]
      (cond (queues/pq-empty? opt-pq)   
              (do (util/assert-is (= sol-cost Double/POSITIVE_INFINITY)) nil)
	    (>= (* wt (second (queues/pq-peek-min opt-pq))) sol-cost)
	      [sol (- sol-cost)]
	    :else
	(let [n (if (< (second (queues/pq-peek-min sub-pq)) sol-cost)
		    (remove-min-from-queues! sub-pq opt-pq)
		  (remove-min-from-queues! opt-pq sub-pq))
	      n-sol (extract-optimal-solution n)]
	  (doseq [c (immediate-refinements n)]
	    (add-to-graph-queues! opt-pq opt-pf sub-pq sub-pf c))
	  (if (and n-sol (< (- (second n-sol)) sol-cost))
	      (recur (first n-sol) (- (second n-sol)))
	    (recur sol sol-cost)))))))







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


  
