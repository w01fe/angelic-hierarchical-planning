(ns edu.berkeley.ai.angelic.hierarchies.offline-algorithms
  (:use edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [search :as search]]
	    [edu.berkeley.ai.util.queues :as queues]
	    [edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts])
  )
  

;;; Algorithm from ICAPS 07 paper, modulo Act simplification


(defn concat-solutions [sols]
;  (println sols)
  [(apply concat nil (map first sols))
   (reduce + 0 (map second sols))])

(defn make-singleton-pq [n]
  (let [pq (queues/make-stack-pq)]
    (queues/pq-add! pq (assoc n :depth 0) 0)
    pq))

(defn hierarchical-forward-search "Node ref fn and graph must be set properly to mimic ICAPS07 behavior"
  ([node] 
     (assert (= false (:graph? (:alt node))))
     (assert (= false (:cache? (:alt node))))
     (hierarchical-forward-search node 0 (make-singleton-pq node) [] [] 0 #{}))
  ([cur-node d pq rest-nodes-with-blacksets prims rew blackset]
     (util/timeout)
     (if (queues/pq-empty? pq) 
         (recur cur-node (inc d) (make-singleton-pq cur-node) rest-nodes-with-blacksets prims rew blackset) 
       (let [next          (queues/pq-remove-min! pq)
	     succeeds-opt? (> (search/upper-reward-bound next) Double/NEGATIVE_INFINITY)]
	 (if (or (not succeeds-opt?) (> (:depth next) d))
	     (recur cur-node d pq rest-nodes-with-blacksets prims rew blackset)
	   (if-let [[acts acts-rew] (search/extract-a-solution next)]
	       (if (empty? rest-nodes-with-blacksets)
;		   (do (println "SOL!" prims acts rew acts-rew)
		       [(concat prims acts) (+ rew acts-rew)];)
		 (let [[[next-node next-blackset] & more-nbs] rest-nodes-with-blacksets]
		   (recur next-node 0 (make-singleton-pq next-node) more-nbs (concat prims acts) (+ rew acts-rew) next-blackset)))
	     (let [succeeds-pess? (> (search/lower-reward-bound next) Double/NEGATIVE_INFINITY)
		   key            (util/safe-get next :plan)] ;; TODO: specific to ALTs)]
	       (if (and succeeds-pess? (not (contains? blackset key)))
		   (let [[first-part & rest-parts] (alts/decompose-plan next)]
		     (recur first-part 0 (make-singleton-pq first-part)
			    (concat 
			     (map #(vector % (conj blackset key (util/safe-get % :plan))) rest-parts)
			     rest-nodes-with-blacksets)
			    prims rew (conj blackset key (util/safe-get first-part :plan))))
		 (do (doseq [ref (search/immediate-refinements next)]
		       (queues/pq-add! pq (assoc ref :depth (inc (:depth next))) 0))
		     (recur cur-node d pq rest-nodes-with-blacksets prims rew blackset))))))))))


(defn plan-max-level [node hla-map]
  (reduce max (map #(if (hla-primitive? %) 0 (util/safe-get hla-map (first (hla-name %)))) (search/node-plan node))))


(defn new-hierarchical-forward-search 
  "New version of HFS that only commits when an HLA has been refined to a lower level.  This eliminates the 
   need for blacksets, and ensures that progress is made when a commitment happens."
  ([node hla-map] 
     (assert (= false (:graph? (:alt node))))
     (assert (= false (:cache? (:alt node))))
     (new-hierarchical-forward-search node 0 (make-singleton-pq node) [] [] 0  hla-map))
  ([cur-node d pq rest-nodes prims rew hla-map]
     (util/timeout)
     (if (queues/pq-empty? pq) 
         (recur cur-node (inc d) (make-singleton-pq cur-node) rest-nodes prims rew hla-map) 
       (let [next          (queues/pq-remove-min! pq)]
;	 (println "consider " (map hla-name (search/node-plan next)))
	 (if (or (not (> (search/upper-reward-bound next) Double/NEGATIVE_INFINITY)) (> (:depth next) d))
	     (recur cur-node d pq rest-nodes prims rew hla-map)
	   (if-let [[acts acts-rew] (search/extract-a-solution next)]
  	       (if (empty? rest-nodes)
		   [(concat prims acts) (+ rew acts-rew)];)
		 (let [[next-node & more-nodes] rest-nodes]
		   (recur next-node 0 (make-singleton-pq next-node) more-nodes (concat prims acts) (+ rew acts-rew) hla-map)))
	     (if (and (< (plan-max-level next hla-map) (plan-max-level cur-node hla-map))
		      (> (search/lower-reward-bound next) Double/NEGATIVE_INFINITY))
	         (let [[first-part & rest-parts] (alts/decompose-plan next)]
;		   (println "commit!" (map hla-name (search/node-plan next)))
		   (recur first-part 0 (make-singleton-pq first-part)
			  (concat rest-parts rest-nodes)
			  prims rew hla-map))
	       (do (doseq [ref (search/immediate-refinements next)]
		     (queues/pq-add! pq (assoc ref :depth (inc (:depth next))) 0))
		   (recur cur-node d pq rest-nodes prims rew hla-map)))))))))

; (let [h (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))) rlm {(first (hla-name (first h))) 11 'act 10 'move-blocks 9 'move-block 8 'move-to 7 'navigate 6 'nav 5}   n (alt-node h {:ref-choice-fn (make-first-maximal-choice-fn rlm) :cache? false :graph? false})]   (time-limit (map :name (first (new-hierarchical-forward-search n rlm))) 30))

; (def *e* (make-random-nav-switch-strips-env 5 2))
; (let [h (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify *e*)) rlm {(first (hla-name (first h))) 11 'act 10 'go 6 'nav 5}   n (alt-node h {:ref-choice-fn (make-first-maximal-choice-fn rlm) :cache? false :graph? false})]   (time-limit (map :name (first (hierarchical-forward-search n))) 30))

(comment 
 ; old, nicer but stack-blowing version
(defn hierarchical-forward-search "Node ref fn and graph must be set properly to mimic ICAPS07 behavior"
  ([node] (hierarchical-forward-search node #{}))
  ([node blackset]
   (some 
    (fn [d]
     (let [pq  (queues/make-stack-pq)]
      (queues/pq-add! pq (assoc node :depth 0) 0)
      (loop []
	(when-not (queues/pq-empty? pq)
	  (let [next          (queues/pq-remove-min! pq)
		succeeds-opt? (> (search/upper-reward-bound next) Double/NEGATIVE_INFINITY)]
	    (if (or (not succeeds-opt?) (> (:depth next) d))
		(recur)
	      (or (search/extract-a-solution next)
		  (let [succeeds-pess? (> (search/lower-reward-bound next) Double/NEGATIVE_INFINITY)
			key            (util/safe-get next :plan)] ;; TODO: specific to ALTs)]
		    (if (and succeeds-pess? (not (contains? blackset key)))
			(concat-solutions 
			 (map 
			  #(hierarchical-forward-search % (conj blackset key (util/safe-get % :plan)))
			  (alts/decompose-plan next)))
		      (do (doseq [ref (search/immediate-refinements next)]
			    (queues/pq-add! pq (assoc ref :depth (inc (:depth next))) 0))
			  (recur)))))))))))
    (iterate inc 0)))))
   
(comment 
  (time-limit (map :name (first (hierarchical-forward-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))) {:ref-choice-fn (make-first-maximal-choice-fn '{act 10 move-blocks 9 move-block 8 move-to 7 navigate 6 nav 5}) :cache? false :graph? false})))) 30)

  (time-limit (map :name (first (hierarchical-forward-search (alt-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-random-nav-switch-strips-env 4 2))) {:ref-choice-fn (make-first-maximal-choice-fn '{act 10 go 7 nav 5}) :cache? false :graph? false})))) 10)
  )





;;; Algorithms from ICAPS 08 paper


;; TODO: ???
(defn aha-star-priority-fn [x] 
  (- 0
     (search/upper-reward-bound x)
     (/ (max (search/lower-reward-bound x) -999999.0) 1000000.0)
     (/ (min (search/node-depth x) 1000000) 10000000000.0)))

(defn aha-star-search  "AHA*.  Identical to A* up to tiebreaking.  Assumes integer costs."
  [node]
  (search/first-optimal-solution node (queues/make-tree-search-pq) aha-star-priority-fn))


;; TODO: check up on threshold updating  (right now, commits to monotonic seq)
(defn ahss-search "Pass a *finite* threshold"
  ([node] (ahss-search node (- Double/MAX_VALUE)))
  ([node threshold] (ahss-search node threshold alts/icaps-priority-fn))
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
					 great-refs)
				alts/first-choice-fn)]
			   (util/sref-set! threshold (search/lower-reward-bound best-ref)) ;; TODO??
;			   (println "committing to " (search/node-str best-ref))
;			   (println "options were: " (map #(vector (search/node-str %) (search/reward-bounds %)) great-refs))
;			   (println)
			   (queues/pq-remove-all! pq)
			   (queues/pq-add! pq best-ref (priority-fn best-ref)))
		       (doseq [ref good-refs]
		         (queues/pq-add! pq ref (priority-fn ref))))
		     (recur)))))))))))

  
     

;;; New versions of ICAPS 08 that include decompose.


(defn aha-star-et-search  "Like AHA*, but returns first provably optimal (possibly high-level) plan *node*, or primitive solution."
  [node]
  (let [pq (queues/make-tree-search-pq)]
    (queues/pq-add! pq node (aha-star-priority-fn node))
    (loop [first? true]
      (when-not (queues/pq-empty? pq)
	(let [next (queues/pq-remove-min! pq)]
;	  (println (search/node-str next))
	  (if (search/dead-end? next) 
	      (recur false)
	    (or (search/extract-optimal-solution next)
		(and (not first?)
		     (= (search/upper-reward-bound next) (search/lower-reward-bound next))
		     next)
		(do 
		  (doseq [ref (search/immediate-refinements next)]
;		    (println "ref " (search/node-str ref))
		    (queues/pq-add! pq ref (aha-star-priority-fn ref)))
		  (recur false)))))))))

(defn aha-star-decomposed-search 
  [node]
  (if-let [result (aha-star-et-search node)]
    (if (isa? (:class result) ::search/Node)
        (if (> (alts/alt-node-hla-count result) 1)
	    (concat-solutions (map aha-star-decomposed-search (alts/decompose-plan result)))
	  (recur (search/reroot-at-node node))))))


(defn ahss-et-search "Pass a *finite* threshold"
  ([node] (ahss-et-search node (- Double/MAX_VALUE)))
  ([node threshold] (ahss-et-search node threshold alts/icaps-priority-fn))
  ([node threshold priority-fn]
 ;    (println (search/node-plan-length node) (alts/alt-node-hla-count node))
     (let [pq        (queues/make-tree-search-pq)
	   [sol rew] (search/extract-a-solution node)]
       (queues/pq-add! pq node (priority-fn node))
       (when (>= (search/upper-reward-bound node) threshold)  ; Handle degenerate
	 (if (and rew (>= rew threshold)) [sol rew]           ; cases
  	   (loop [first? true threshold threshold]
	     (when-not (queues/pq-empty? pq)
	       (let [next (queues/pq-remove-min! pq)  ; Has no imm. sol, upper >= thresh
		     refs (search/immediate-refinements next)
		     good-refs (filter #(>= (search/upper-reward-bound %) threshold) refs)
		     sols      (filter identity (map search/extract-a-solution good-refs))
		     good-sols (seq (filter #(>= (second %) threshold) sols))]
		 (if good-sols  ; Found a good enough primitive refinement
		     (util/first-maximal-element second good-sols)
                   (if-let [great-refs (seq (filter #(>= (search/lower-reward-bound %) threshold) good-refs))]
		       (util/first-maximal-element ; tie break
			#(+ (search/lower-reward-bound %) (/ (search/upper-reward-bound %) 100000.0))
			great-refs)
;			 (println "committing to " (search/node-str best-ref))
		     (do
		       (doseq [ref good-refs]
		         (queues/pq-add! pq ref (priority-fn ref)))
		       (recur false threshold))))))))))))

(defn ahss-decomposed-search 
  ([node] (ahss-decomposed-search node (- Double/MAX_VALUE)))
  ([node threshold] (ahss-decomposed-search node threshold alts/icaps-priority-fn))
  ([node threshold priority-fn]
  (if-let [result (ahss-et-search node threshold priority-fn)]
    (if (isa? (:class result) ::search/Node)
        (if (> (alts/alt-node-hla-count result) 1)
	    (concat-solutions (map #(ahss-decomposed-search % (search/lower-reward-bound %) priority-fn)
				   (alts/decompose-plan result)))
	  (recur (search/reroot-at-node node) (search/lower-reward-bound node) priority-fn))))))




;;; New algorithm - weighted aha-star search.

(defn weighted-aha-star-search  "AHA*.  Identical to A* up to tiebreaking.  Assumes integer costs."
  [node wt]
  (search/first-optimal-solution node (queues/make-tree-search-pq) 
				 (alts/get-weighted-aha-star-priority-fn wt)))


;;; New algorithm - optimistic-aha-star-search; based on Thayer+Ruml, ICAPS 08
; Like ahss, but threshold is a multiplier of hierarchically optimal solution reward.

(defn- add-to-queues! [prim-pq prim-pf sec-pq sec-pf item]
    (queues/pq-add! prim-pq item (prim-pf item))
    (queues/pq-add! sec-pq item (sec-pf item)))

(defn- remove-min-from-queues! [prim-pq sec-pq]
  (let [item (queues/pq-remove-min! prim-pq)]
    (queues/pq-remove! sec-pq item)
    item))

(defn optimistic-aha-star-search 
  ([node wt sub-pf] (optimistic-aha-star-search node wt sub-pf false false))
  ([node wt sub-pf decompose? et?]
  (let [opt-pf (fn negator [x] (- (search/upper-reward-bound x)))
	opt-pq (queues/make-fancy-tree-search-pq)
	sub-pq (queues/make-fancy-tree-search-pq)]
    (add-to-queues! opt-pq opt-pf sub-pq sub-pf node)
    (loop [sol nil, sol-lb (+ 0 Double/POSITIVE_INFINITY), sol-pri (+ 0 Double/POSITIVE_INFINITY)]
      (cond (queues/pq-empty? opt-pq)   
              (do (util/assert-is (= sol-lb Double/POSITIVE_INFINITY)) nil)
	    (>= (* wt (queues/pq-peek-min opt-pq)) sol-lb)
	      (do (util/print-debug 2 "committing to " (search/node-str sol))
		  (if et? sol
		    ((if decompose? ahss-decomposed-search ahss-search) 
		     (search/reroot-at-node sol alts/first-choice-fn) (- sol-lb) sub-pf)))
	    :else
	(let [n (if (< (queues/pq-peek-min sub-pq) sol-pri)
		    (remove-min-from-queues! sub-pq opt-pq)
		  (remove-min-from-queues! opt-pq sub-pq))
	      n-lb (search/lower-reward-bound n)]
;	  (println (search/node-str n) (opt-pf n) (sub-pf n))
	  (doseq [c (search/immediate-refinements n)]
;	      (println (node-str n) (node-str c) (opt-pf c) (sub-pf c))
	    (add-to-queues! opt-pq opt-pf sub-pq sub-pf c))
	  (if (< (- n-lb) sol-lb)
	      (recur n (- n-lb) (sub-pf n))
	    (recur sol sol-lb sol-pri))))))))

(defn streaming-search 
  "Refine provided plan (node) using AHSS.
   Returns a lazy seq of result actions, but no final cost.
   The user may want to call seque on the resulting sequence, to realize it in the background."
  ([node]
    (if (isa? (:class node) ::search/Node)
        (apply concat
	  (for [result (alts/decompose-plan node)]
	    (streaming-search (ahss-et-search result (search/lower-reward-bound result)))))
      (first node))))



(comment 

 (do (reset-ref-counter) (println (second (time (aha-star-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))))))) (sref-get *ref-counter*)))

(do (reset-ref-counter) (println (second (time (optimistic-aha-star-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))) {:ref-choice-fn icaps-choice-fn}) 2 (get-weighted-aha-star-priority-fn 100)))) (sref-get *ref-counter*)))

(interactive-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))) {:ref-choice-fn icaps-choice-fn}) (make-tree-search-pq) (get-weighted-aha-star-priority-fn 10))
)

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
	   graph?      [false true]
	   [sf-n alg strict?] [["aha" aha-star-search true] ["ahss-inf" ahss-search false] ["ahss-=" #(ahss-search % rew) true]]]
     (util/testing (str inst-n " " cache? " " graph? " " sf-n)
;       (println inst-n cache? graph? sf-n)
       (util/is ((if strict? = >=) rew  
	 (second (envs/check-solution env (alg (alts/alt-node (get-hierarchy h env) {:cache? cache? :graph? graph?})))))))))


      




(comment 
 (dotimes [_ 2] (let [env (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 20 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))] (doseq [h [*nav-switch-hierarchy* *nav-switch-hierarchy-improved*]] (let [node (get-hierarchy h env )] (println h) (dotimes [_ 1] (time (println (second (aha-star-search (alt-node node))))) (time (println (second (ahss-search (alt-node node))))) )))))
 )


  
