(ns edu.berkeley.ai.angelic.hierarchies.offline-algorithms
  (:use edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [search :as search]]
	    [edu.berkeley.ai.util.queues :as queues]
	    [edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts])
  )
  

;;; Algorithm from ICAPS 07 paper, modulo Act simplification


;; With decompose


; Add decompose operation to ALTs.
(defn hierarchical-forward-search "Node ref fn must be set properly to mimic ICAPS07 behavior"
  ([node] (hierarchical-forward-search node #{}))
  ([node blackset]
   (let [pq  (queues/make-stack-pq)]
    (queues/pq-add! pq node 0)
    (loop []
      (when-not (queues/pq-empty? pq)
	(let [next          (queues/pq-remove-min! pq)
	      succeeds-opt? (> (search/upper-reward-bound next) Double/NEGATIVE_INFINITY)]
	  (if (not succeeds-opt?)
	      (recur)
	    (or (search/extract-a-solution next)
		(let [succeeds-pess? (> (search/lower-reward-bound next) Double/NEGATIVE_INFINITY)
		      key            (util/safe-get node :plan)] ;; TODO: specific to ALTs)]
		  (if (and succeeds-pess? (not (contains? blackset key)))
  		      (mapcat 
		       #(hierarchical-forward-search % (conj blackset key (util/safe-get % :plan)))
		       (alts/decompose-plan node))
		    (do (doseq [ref (search/immediate-refinements next)]
			  (queues/pq-add! pq ref 0))
			(recur))))))))))))


;; Also without decompose

(defn simple-hierarchical-forward-search "Node ref fn must be set properly to mimic ICAPS07 behavior"
  [node]
  (let [pq  (queues/make-stack-pq)]
    (queues/pq-add! pq node 0)
    (loop []
      (when-not (queues/pq-empty? pq)
	(let [next          (queues/pq-remove-min! pq)
	      succeeds-opt? (> (search/upper-reward-bound next) Double/NEGATIVE_INFINITY)]
	  (if (not succeeds-opt?)
	      (recur)
	    (or (search/extract-a-solution next)
		(let [succeeds-pess? (> (search/lower-reward-bound next) Double/NEGATIVE_INFINITY)
		      next           (if succeeds-pess?
				       (do (queues/pq-remove-all! pq)
					   (search/reroot-at-node next))
				       next)]
		  (doseq [ref (search/immediate-refinements next)]
		    (queues/pq-add! pq ref 0))
		  (recur)))))))))



;;; Algorithms from ICAPS 08 paper

(defn aha-star-search  "AHA*.  Identical to A* up to tiebreaking.  Assumes integer costs."
  [node]
  (search/first-optimal-solution node (queues/make-tree-search-pq)  
    (fn cost-fn [x] 
      (- 0
	 (search/upper-reward-bound x)
	 (/ (max (search/lower-reward-bound x) -999999.0) 1000000.0)))))


;; TODO: check up on threshold updating  (right now, commits to monotonic seq)
(defn ahss-search "Pass a *finite* threshold"
  ([node] (ahss-search node (- Double/MAX_VALUE)))
  ([node threshold] (ahss-search node threshold alts/icaps-priority-fn))
;		      (fn ahss-priority-fn [node]
;			(- 0 
;			   (search/upper-reward-bound node)
;			   (max (search/lower-reward-bound node) -1000000.0)))))
  ([node threshold priority-fn]
     (let [pq        (queues/make-tree-search-pq)
	   [sol rew] (search/extract-a-solution node)
	   threshold (util/sref threshold)]
          
       (queues/pq-add! pq node (priority-fn node))
       (when (>= (search/upper-reward-bound node) (util/sref-get threshold))  ; Handle degenerate
	 (if (and rew (>= rew (util/sref-get threshold))) [sol rew]           ; cases
  	   (loop []
	     (when-not (queues/pq-empty? pq)
	       (let [next (queues/pq-remove-min! pq)  ; Has no imm. sol, upper >= thresh
		     refs (search/immediate-refinements next)
		     good-refs (filter #(>= (search/upper-reward-bound %) (util/sref-get threshold)) refs)
		     sols      (filter identity (map search/extract-a-solution good-refs))
		     good-sols (seq (filter #(>= (second %) (util/sref-get threshold)) sols))]
;		 (println (search/node-str next) (search/reward-bounds next))
		 (if good-sols  ; Found a good enough primitive refinement
		     (util/first-maximal-element second good-sols)
		   (do
                     (if-let [great-refs (seq (filter #(>= (search/lower-reward-bound %) (util/sref-get threshold)) good-refs))]
		         (let [best-ref 
			       (search/reroot-at-node
				(util/first-maximal-element ; tie break
;					 search/lower-reward-bound 
					 #(+ (search/lower-reward-bound %) (/ (search/upper-reward-bound %) 100000.0))
					 great-refs))]
			   (util/sref-set! threshold (search/lower-reward-bound best-ref)) ;; TODO??
;			   (println "committing to " (search/node-str best-ref))
;			   (println "options were: " (map #(vector (search/node-str %) (search/reward-bounds %)) great-refs))
;			   (println)
			   (queues/pq-remove-all! pq)
			   (queues/pq-add! pq best-ref (priority-fn best-ref)))
		       (doseq [ref good-refs]
		         (queues/pq-add! pq ref (priority-fn ref))))
		     (recur)))))))))))

     




;; Testing




(require '[edu.berkeley.ai.envs :as envs])
(require '[edu.berkeley.ai.domains.nav-switch :as nav-switch])
(require '[edu.berkeley.ai.domains.strips :as strips])
(require '[edu.berkeley.ai.domains.warehouse :as warehouse])
(require '[edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts])
(require '[edu.berkeley.ai.search.algorithms.textbook :as textbook])

(def *ns-inst* ["ns" -27 nav-switch/*nav-switch-hierarchy* 
		(strips/constant-predicate-simplify
		 (nav-switch/make-nav-switch-strips-env 6 6 [[4 0] [3 3] [0 4]] [5 0] true [0 5]))])

(def *wh-inst* ["wh" -6 warehouse/*warehouse-hierarchy*
		 (strips/constant-predicate-simplify 
		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[c] 3 '[d]} nil ['[b d]]))])
;		  (warehouse/make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))])
;		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[d] 3 '[c]} nil ['[a b c]]))])


(util/deftest hierarchical-algorithms
   (doseq [[inst-n rew h env] [*ns-inst* *wh-inst*]
	   cache?      [false true]
	   graph?      [false true :full]
	   [sf-n alg strict?] [["aha" aha-star-search true] ["ahss-inf" ahss-search false] ["ahss-=" #(ahss-search % rew) true]]]
     (util/testing (str inst-n " " cache? " " graph? " " sf-n)
;       (println inst-n cache? graph? sf-n)
       (util/is ((if strict? = >=) rew  
	 (second (envs/check-solution env (alg (alts/alt-node (get-hierarchy h env) cache? graph?)))))))))


      




(comment 
 (dotimes [_ 2] (let [env (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 20 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))] (doseq [h [*nav-switch-hierarchy* *nav-switch-hierarchy-improved*]] (let [node (get-hierarchy h env )] (println h) (dotimes [_ 1] (time (println (second (aha-star-search (alt-node node))))) (time (println (second (ahss-search (alt-node node))))) )))))
 )


  
