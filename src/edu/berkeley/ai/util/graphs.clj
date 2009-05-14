(ns edu.berkeley.ai.util.graphs
  (:import [java.util HashSet HashMap LinkedList])
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.queues edu.berkeley.ai.util.disjoint-sets)
  )

;;;; Incremental directed acyclic graphs for cycle detection (only).

; For now, only keep track of edges in forward direction.
; Simplest possible implementation (for now), don't keep track of anything.
; A DAG is just a map from node labels (arbitrary objects) to sets of child node labels.

(defn make-empty-dag [] {})

(defn dag-children [dag s] (get dag s #{}))

(defn dag-descendant? [dag s t]
  (or (= s t)
      (let [open (LinkedList. [s]) closed (HashSet.)]
	(loop []
	  (when-not (.isEmpty open)
	    (let [f (.remove open)]
	      (if (.contains closed f)
		  (recur)
		(let [desc (dag-children dag f)]
		  (or (contains? desc t)
		      (do (.addAll open desc) 
			  (.add closed f)
			  (recur)))))))))))
;    (loop [open #{s} closed #{}]
;      (when-first [f open]
;	(let [r (disj open f)]
;	  (if (contains? closed f)
;	      (recur r closed)
;	    (let [desc (get dag f #{})]
;	      (or (contains? desc t)
;		  (recur (into r desc) (conj closed f))))))))))

(defn dag-add-edge [dag s t]
  (assert (not (dag-descendant? dag t s)))
  (assoc dag s (conj (get dag s #{}) t)))

(deftest test-dag
  (is (dag-descendant?  (make-empty-dag) 'a 'a))
  (is (not (dag-descendant? (make-empty-dag) 'a 'b)))
  (is (not (dag-descendant? (-> (make-empty-dag) (dag-add-edge 'b 'a)) 'a 'b)))
  (is (dag-descendant? (-> (make-empty-dag) (dag-add-edge 'a 'b)) 'a 'b))
  (is (dag-descendant? (-> (make-empty-dag) (dag-add-edge 'a 'b) (dag-add-edge 'b 'c)) 'a 'c))
  (is (not (dag-descendant? (-> (make-empty-dag) (dag-add-edge 'a 'b) (dag-add-edge 'c 'b)) 'a 'c))))
  


;;;; Undirected graphs, shortest paths, spanning trees, etc.

; nodes is a set of nodes, edges is a map from sets of edges to costs

(defstruct undirected-graph :class :nodes :edges)

(defn edge-cost [g n1 n2]
  (get (:edges g) #{n1 n2} Double/POSITIVE_INFINITY))

(defn- make-undirected-graph- [nodes edges]
  (struct undirected-graph ::UndirectedGraph nodes edges))

(defn make-undirected-graph [nodes edges]
  (assert-is (set? nodes))
  (assert-is (map? edges))
  (doseq [[e c] edges]
    (assert-is (number? c))
    (assert-is (>= c 0))
    (assert-is (set? e))
    (assert-is (= (count e) 2))
    (assert-is (every? nodes e)))
  (make-undirected-graph- nodes edges))

(defn shortest-path-graph "Get the graph of shortest paths." [g]
  (let [{:keys [nodes edges]} g
	n   (count nodes)
	nv  (vec nodes)
	paths (make-array Object (* n n))]
    (doseq [i (range n), j (range n)]
      (aset paths (+ (* i n) j) (edge-cost g (nth nv i) (nth nv j))))
    (doseq [i (range n)]
      (aset paths (+ (* i n) i) 0))
    (doseq [k (range n), i (range n), j (range n)]
      (aset paths (+ (* i n) j)
	    (min (aget paths (+ (* i n) j))
		 (+ (aget paths (+ (* i n) k))
		    (aget paths (+ (* k n) j))))))
    (make-undirected-graph-
     nodes
     (into {}
       (for [i (range n), j (range i) 
	     :let [c (aget paths (+ (* i n) j))]
	     :when (< c Double/POSITIVE_INFINITY)]
	 [#{(nth nv i) (nth nv j)} c])))))


(defn sub-graph [g node-subset]
  (let [{:keys [nodes edges]} g]
    (assert-is (every? nodes node-subset))
    (assert-is (set? node-subset))
    (make-undirected-graph- node-subset edges)))

(defn minimum-spanning-tree "returns [MST cost]" [g]
  (let [{:keys [nodes edges]} g
	n (dec (count nodes))
	q (make-tree-search-pq)
	ds (make-disjoint-sets (seq nodes))]
    (doseq [[es c] edges]
      (when (every? nodes es)
	(pq-add! q es c)))
    (loop [em {}
	   c  0]
      (cond (= (count em) n) [(make-undirected-graph- nodes em) c]
	    (pq-empty? q)    [nil Double/POSITIVE_INFINITY]
	    :else
	(let [[e ec] (pq-remove-min-with-cost! q)]
	  (let [[n1 n2] (seq e)]
	    (if (ds-separate? ds n1 n2)
	        (do
		  (ds-union ds n1 n2)
		  (recur (assoc em e ec)
			 (+ c ec)))
	      (recur em c))))))))
	  

    

  
  

       
  
  

