(ns angel.search.algorithms.textbook
  (:refer-clojure)
  (:use angel.search clojure.contrib.test-is)
  )

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


