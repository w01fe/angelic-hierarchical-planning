(ns edu.berkeley.ai.angelic.hierarchies.algorithms
  (:use edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [search :as search]]
	    [edu.berkeley.ai.util.queues :as queues]
	    [edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts])
  )
  

(defn aha-star-search  "AHA*.  Identical to A* up to tiebreaking.  Assumes integer costs."
  [node]
  (search/first-optimal-solution node (queues/make-tree-search-pq)  
    (fn cost-fn [x] 
      (- 0
	 (search/upper-reward-bound x)
	 (/ (max (search/lower-reward-bound x) -999999.0) 1000000.0)))))


; TODO: this priority fn won't work well on hard domains -- need to take portion with
 ; non-inf pessimistic value into account ...
(defn ahss-search "Pass a *finite* threshold"
  ([node] (ahss-search node (- Double/MAX_VALUE)))
  ([node threshold] (ahss-search node threshold alts/icaps-priority-fn))
;		      (fn ahss-priority-fn [node]
;			(- 0 
;			   (search/upper-reward-bound node)
;			   (max (search/lower-reward-bound node) -1000000.0)))))
  ([node threshold priority-fn]
     (let [pq        (queues/make-tree-search-pq)
	   [sol rew] (search/extract-a-solution node)]
       (queues/pq-add! pq node (priority-fn node))
       (when (>= (search/upper-reward-bound node) threshold)  ; Handle degenerate
	 (if (and rew (>= rew threshold)) [sol rew]           ; cases
  	   (loop []
	     (when-not (queues/pq-empty? pq)
	       (let [next (queues/pq-remove-min! pq)  ; Has no imm. sol, upper >= thresh
		     refs (search/immediate-refinements next)
		     good-refs (filter #(>= (search/upper-reward-bound %) threshold) refs)
		     sols      (filter identity (map search/extract-a-solution good-refs))
		     good-sols (filter #(>= (second %) threshold) sols)]
;		 (println (search/node-str next))
		 (if good-sols  ; Found a good enough primitive refinement
		     (util/first-maximal-element second good-sols)
		   (do
                     (if-let [great-refs (filter #(>= (search/lower-reward-bound %) threshold) good-refs)]
		         (let [best-ref 
			       (alts/clear-alt-graph-cache
				(util/first-maximal-element ; tie break
;					 search/lower-reward-bound 
					 #(+ (search/lower-reward-bound %) (/ (search/upper-reward-bound %) 100000.0))
					 great-refs))]
;			   (println "committing to " (search/node-str best-ref))
;			   (println "options were: " (map #(vector (search/node-str %) (search/reward-bounds %)) great-refs))
;			   (println)
;			   (alts/clear-alt-graph-cache best-ref)
			   (queues/pq-remove-all! pq)
			   (queues/pq-add! pq best-ref (priority-fn best-ref)))
		       (doseq [ref good-refs]
		         (queues/pq-add! pq ref (priority-fn ref))))
		     (recur)))))))))))

     

(comment 
 (dotimes [_ 2] (let [env (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 20 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))] (doseq [h [*nav-switch-hierarchy* *nav-switch-hierarchy-improved*]] (let [node (get-hierarchy h env )] (println h) (dotimes [_ 1] (time (println (second (aha-star-search (alt-node node))))) (time (println (second (ahss-search (alt-node node))))) )))))
 )


  