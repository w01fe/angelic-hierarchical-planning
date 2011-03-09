(ns angelic.util.graphs
  (:import [java.util Stack HashSet Map HashMap LinkedList ArrayList])
  (:use clojure.test angelic.util angelic.util.queues angelic.util.disjoint-sets
        angelic.util.lp))

;;;; Incremental directed acyclic graphs for cycle detection (only).

; For now, only keep track of edges in forward direction.
; Simplest possible implementation (for now), don't keep track of anything.
; A DAG is just a map from node labels (arbitrary objects) to sets of child node labels.

 
(defn edge-list->incoming-map [edges]
  (map-vals #(map first %) (group-by second edges)))

(defn edge-list->outgoing-map [edges]
  (map-vals #(map second %) (group-by first edges)))

(defn outgoing-map->edge-list [outgoing-map]
  (for [[k vs] outgoing-map, v vs] [k v]))

(defn incoming-map->edge-list [incoming-map]
  (for [[k vs] incoming-map, v vs] [v k]))

(defn invert-edges [edges] (for [[s t] edges] [t s]))

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
  (if (= n1 n2) 0
      (get (:edges g) #{n1 n2} Double/POSITIVE_INFINITY)))

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
	  

    
;;;;;;;;;;;;;;; Simple a'la carte algorithms that operate on edge lists, etc. ;;;;;;;;;;;;;;;;;;


; TODO: should really just return a vector for clusters...
(defn scc-graph 
  "Take an edge list and return [edge-list node-set-map] for graph of sccs. Pretends every node has self-loop.  Clusters returned will be in topological order."
  [edges]
  (let [edges (distinct (concat edges (map (fn [x] [x x]) (apply concat edges))))
        pe (merge (into {} (map vector (map second edges) (repeat nil))) 
                  (map-vals #(map second %) (group-by first edges)))
        e  (HashMap. #^Map pe)
        re (HashMap. #^Map (map-vals #(map first %) (group-by second edges)))
        s (Stack.)]
    (while (not (.isEmpty e))
     ((fn dfs1 [n]
        (when (.containsKey e n) 
          (let [nns (.get e n)]
            (.remove e n)
            (doseq [nn nns] (dfs1 nn)))
          (.push s n)))
      (first (keys e))))
;    (println s pe e re)
    (let [sccs (into (sorted-map) 
                 (indexed
                  (remove empty?
                          (for [n (reverse (seq s))]
                            ((fn dfs2 [n]
                               (when (.containsKey re n)
                                 (let [nns (.get re n)]
                                   (.remove re n)              
                                   (cons n (apply concat (doall (map dfs2 nns)))))))
                             n)))))
          rev-sccs (into {} (for [[k vs] sccs, v vs] [v k]))]
      [(distinct 
         (for [[scc nodes] sccs
               node nodes
               outgoing (get pe node)
               :let [n-scc (get rev-sccs outgoing),
                     _     (assert (<= scc n-scc))]]
           [scc n-scc]))
       sccs])))

(defn dag? "Is this a dag, ignoring self-loops." [edges]
  (every? singleton? (vals (second (scc-graph edges)))))

(defn tree? "Is this connected graph a tree?, paying attn to self loops" [edges]
  (->> edges 
       (remove #(apply = %))
       (group-by second)
       vals
       (every? singleton?)))

(defn inverted-tree? [edges] (tree? (invert-edges edges)))

(defn transitive-closure-map [edge-map]
  (assert (dag? (for [[k vs] edge-map, v vs] [k v])))
  (let [d-fn (memoized-fn descendent-set [node]
                          (->> (edge-map node)
                               (remove #{node})
                               (map descendent-set)
                               (apply clojure.set/union (edge-map node))))]
    (into {} (for [k (keys edge-map)] [k (d-fn k)]))))

(defn transitive-closure [edges]
  (-> edges edge-list->outgoing-map transitive-closure-map outgoing-map->edge-list))

(defn transitive-reduction [edges]
;  (assert (dag? edges))
  (let [edge-map (edge-list->outgoing-map edges)
        tcm      (transitive-closure-map edge-map)]
    (apply concat
      (for [[s ts] edge-map]
        (loop [desc #{} ts ts edges []]
          (if (empty? ts) edges
            (let [[t & rt] ts]
;              (println s t desc)
              (cond (= s t)  (recur desc rt (cons [s t] edges))
                    (desc t) (recur desc rt edges)
                    :else  (recur (union-coll desc (tcm t)) rt (cons [s t] edges))))))))))

(defn tree-reducible? [edges] (tree? (transitive-reduction edges)))

(defn inverted-tree-reducible? [edges] (tree-reducible? (invert-edges edges)))

(defn topological-sort-indices 
  "Return a map from nodes to integers, where 0 is a source.  Nodes in same SCC will have same val."
  [edges]
  (into {}
    (for [[cn vars] (second (scc-graph edges))
          var vars]
      [var cn])))

(defn postwalk [roots outgoing-map]
  (let [ret (ArrayList.)
        closed (HashSet.)
        walk (fn walk [r]
               (when-not (.contains closed r)
                 (.add closed r)
                 (doseq [c (outgoing-map r)] (walk c))
                 (.add ret r)))]
    (doseq [root roots] (walk root))
    (seq ret)))


(defn df-topological-sort-indices 
  "Return a map from nodes to integers, where 0 is a source.  Nodes in same SCC will have same val.
   Breaks ties with an arbitrary depth-first traversal."
  [edges]
  (let [[scc-edges scc-nodes] (scc-graph edges)
        scc-edges (remove #(apply = %) scc-edges)
        scc-sinks (clojure.set/difference (set (map second scc-edges)) (set (map first scc-edges)))
        inv-scc-map (edge-list->incoming-map scc-edges)
        df-order  (postwalk scc-sinks inv-scc-map)]
;    (println scc-sinks df-order)
    (into {}
     (for [[i comp] (indexed df-order)
           var (safe-get scc-nodes comp)]
       [var i]))))


; Old version, before realized that scc-graph outputs topological order.
;  (println edges)
;  (let [[scc-edges scc-nodes] (scc-graph edges)]
;    (assert-is (dag? scc-edges) "%%" (def *tmp edges))
;    (loop [scc-edges scc-edges, scc-nodes scc-nodes, out {}, i 0]
;      (if (empty? scc-nodes) out
;        (let [source (first (filter (fn [n] (every? (fn [[s t]] (or (= s t) (not= t n))) scc-edges)) (keys scc-nodes)))]        
;          (assert-is (identity source) (str  (vec (map vec [scc-edges scc-nodes]))))
;          (recur (remove (fn [[s t]] (= s source)) scc-edges) (dissoc scc-nodes source)
;                 (into out (map vector (get scc-nodes source) (repeat i))) (inc i)))))))


;; Seems buggy in several ways; just try on 4x3 grid world.  Loses connectivity, voltages are messed up, etc.  
(defn find-shortest-path-stu-edges
  "Take a directed edge list, list of source nodes, and list of target nodes,
   and return a list of edges that may participate in a shortest s->x->t path
   where all edges have unit cost. Usees a circuit-based LP solving method.
   Not sure if this is actually useful for anyone..."
  [edge-list sources sinks]
  (let [nodes     (distinct (apply concat sources sinks edge-list))
        all-nodes (set (concat nodes [::SOURCE ::SINK]))
        all-edges (concat edge-list 
                          (for [source sources] [::SOURCE source])
                          (for [sink sinks]     [sink     ::SINK]))
        out-map   (map-vals #(map second %) (group-by first all-edges)) 
        in-map    (map-vals #(map first %)  (group-by second all-edges))]
    (map key
     (filter #(and (not (all-nodes (key %))) (not (some #{::SOURCE ::SINK} (key %))) (> (val %) 0))
              (first 
                 (solve-lp-clp
                  (make-lp
                   (into {}
                         (concat
                          [[::SOURCE [0 0]]
                           [::SINK   [1 1]]]
                          (for [node nodes]     [node [nil nil]])
                          (for [edge all-edges] [edge [0 nil]])))
                   (into {} (for [edge all-edges] [edge -1])) ; Minimize current
                   (into {}
                         (concat
                          (for [node nodes] ;; Current conservation
                            [(into {}
                                   (concat
                                    (for [in  (in-map node)]  [[in node]   1])
                                    (for [out (out-map node)] [[node out] -1])))
                             [0 0]])
                          (for [[s t :as edge] all-edges] ;; I >= v_t - v_s
                            [{edge 1, s 1, t -1} [0 nil]]))))))))))

(deftest find-shortest-path-stu-edges-complex
  (is (= (set (find-shortest-path-stu-edges [[:s :t] [:t :u] [:t :x]] [:s] [:u])) 
         #{[:s :t] [:t :u]}))
  (is (= (set (find-shortest-path-stu-edges [[:s :t] [:t :u] [:t :x] [:x :t]] [:s] [:u])) 
         #{[:s :t] [:t :u]}))
  (is (= (set (find-shortest-path-stu-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u]] [:s] [:u])) 
         #{[:s :t] [:t :u] [:t :x] [:x :u]} ))  
 #_  (is (= (set (find-shortest-path-stu-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]] [:s] [:u]))
         #{[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]} )))
  
; Node n is reachable from s iff:
 ; some predecessor of n is reachable from s

; Node a is on every path from s to n iff:
 ; a = n, or a is on every path from s to a predecessor of n.

; Node n is acyclic-reachable from s iff:
 ; some predecessor of n w/o n in its every-list is reachable from s

; Node a is on every acyclic path from s to n iff:
 ; a = n, or a is on every path from s to a pred. or n w/o n on its every-list.
; Node a is on every acyclic path from s to n iff:


(defn quiescence-search 
  "Take an edge list, and a function from nodes to initial values.
   update-fn takes a node's name, current value and those of its (incoming) neighbors, in order, and 
   produces an value for this node.  src-vals is a set of [node value] pairs acting as dummy incoming arcs to
   start the process, which continues until each node's value is unchanged. Return a map from
   node names to final values.  Will only contain updates, not init values."
  [edge-list init-fn update-fn src-vals]
  (let [named-srcs   (map vector (repeatedly gensym) src-vals)
        edge-list    (concat (for [[g [s]] named-srcs] [g s]) edge-list)
        incoming-map (edge-list->incoming-map edge-list)
        outgoing-map (edge-list->outgoing-map edge-list)
        node-vals    (HashMap. #^Map (into {} (for [[g [_ v]] named-srcs] [g v])))
        node-val     #(lazy-get node-vals % (init-fn %))
        queue        (LinkedList. (map first src-vals))
        queue-count  (HashMap. (into {} (for [x (map first src-vals)] [x 1])))]

    (while (not (.isEmpty queue))
      (let [node (.removeFirst queue)
            rem-count (dec (.get queue-count node))]
        (.put queue-count node rem-count)
        (when (zero? rem-count)
          (let [old-val (node-val node)
                new-val (apply update-fn node old-val (map node-val (incoming-map node)))]
            (when-not (= new-val old-val)
              (.put node-vals node new-val)
              (doseq [succ (outgoing-map node)] 
                (.addFirst queue succ)
                (.put queue-count succ (inc (get queue-count node 0)))))))))
    
    (apply dissoc (into {} node-vals) (map first named-srcs))))

(defn compute-reachable-nodes-and-necessary-predecessors [edge-list s]
  (quiescence-search edge-list (fn init-fn [_] nil)
    (fn update-fn [node old-val & pred-vals]
      (let [acyclic-reachable-preds (remove #(or (nil? %) (contains? % node)) pred-vals)]
        (when (seq acyclic-reachable-preds)
          (conj (apply clojure.set/intersection acyclic-reachable-preds) node))))
    [[s #{}]]))

(defn eliminate-some-cyclic-edges 
  "Return a list of edges, where those provably on no acyclic s-t path have been eliminated.
   Do so in polynomial time, possibly missing some always-cyclic edges."  
  [edges s t]
  (let [forward-sets  (compute-reachable-nodes-and-necessary-predecessors edges s)
        backward-sets (compute-reachable-nodes-and-necessary-predecessors (map reverse edges) t)]
    (filter
     (fn [[a b]]
       (let [f (forward-sets a)
             b (backward-sets b)]
         (and f b (empty? (clojure.set/intersection f b)))))
     edges)))


(deftest eliminate-some-cyclic-edges-simple-test
  (is (= (set (eliminate-some-cyclic-edges [[:s :t] [:t :u] [:t :x]] :s :u)) 
         #{[:s :t] [:t :u]}))
  (is (= (set (eliminate-some-cyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t]] :s :u)) 
         #{[:s :t] [:t :u]}))
  (is (= (set (eliminate-some-cyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u]] :s :u)) 
         #{[:s :t] [:t :u] [:t :x] [:x :u]} ))  
  (is (= (set (eliminate-some-cyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]] :s :u))
         #{[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]} )))

(defn generate-grid-graph [w h]
  (concat
   (for [x (range 1 w) y (range 1 (inc h))] [[x y] [(inc x) y]])
   (for [x (range 1 w) y (range 1 (inc h))] [[(inc x) y] [x y]])
   (for [x (range 1 (inc w)) y (range 1 h)] [[x y] [x (inc y)]])
   (for [x (range 1 (inc w)) y (range 1 h)] [[x (inc y)] [x y]])))

(deftest eliminate-some-cyclic-edges-grid-test
  (is (= (count (eliminate-some-cyclic-edges (generate-grid-graph 2 2) [1 1] [2 2])) 4))
  (is (= (count (eliminate-some-cyclic-edges (generate-grid-graph 3 3) [1 1] [2 2])) 18))
  )



(defn separator-node-set
  "Return a set of nodes, such that removing these nodes disconnects this (directed) graph."
  [edges]
  (let [ordered-vars (map safe-singleton (vals (second (scc-graph edges))))
        all-vars     (set ordered-vars)
        rnnp         (compute-reachable-nodes-and-necessary-predecessors 
                      (invert-edges edges) (last ordered-vars))
        edge-map     (edge-list->outgoing-map edges)]
    (loop [remaining-vars ordered-vars, necessary-map {}, result #{}]
      (println necessary-map)
      (if (empty? remaining-vars) result
        (let [[var & rest-vars] remaining-vars
              nec               (get necessary-map var)
              next-necessary-map 
                (reduce 
                 (fn [m sv] (update-in m [sv] #(clojure.set/intersection 
                                                (or nec (rnnp var)) (or % all-vars))))
                 necessary-map (edge-map var))]
          (if (or (nil? nec) (contains? nec var))
              (recur rest-vars next-necessary-map (conj result var))
            (recur rest-vars next-necessary-map result)))))))

(defn descendant-set [edges source-nodes]
  (let [edge-map (edge-list->outgoing-map edges)
        h        (HashSet.)]
    (doseq [s source-nodes]
      ((fn helper [n]
         (when-not (.contains h n)
           (.add h n)
           (doseq [nn (edge-map n)]
             (helper nn))))
       s))
    (set h)))

(defn ancestor-set [edges source-nodes]
  (descendant-set (invert-edges edges) source-nodes))

       
  
  

(comment 
  ; Failed attempt
  
  (defn edge-acyclic?
    "Does there exist an acyclic path from a source to a sink that includes key-edge?
   Uses a circuit-based method where resistances are left implicit and variable.
   Due to precision, may fail on graphs with > 1000 nodes.  This almost seems to work,
   but actually fails since constraints allow routing current along cycles 
   (i.e., here, weighting of current cost matters."
    [edge-list key-edge sources sinks]
    (let [nodes     (distinct (apply concat sources sinks edge-list))
          all-nodes (set (concat nodes [::SOURCE ::SINK]))
          all-edges (concat edge-list 
                            (for [source sources] [::SOURCE source])
                            (for [sink sinks]     [sink     ::SINK]))
          free-edges (remove #(= (set %) (set key-edge)) all-edges)
          out-map   (map-vals #(map second %) (group-by first (cons key-edge free-edges))) 
          in-map    (map-vals #(map first %)  (group-by second (cons key-edge free-edges)))]
      (assert (< (count all-nodes) 500))
      (when-let [[sol] (solve-lp-clp
                        (make-lp
                         (into {}
                               (concat
                                [[::SOURCE [0 0]]
                                 [::SINK   [1 1]]
                                 [key-edge [0.001 0.001]]]
                                (for [node nodes]     [node [nil nil]])
                                (for [edge free-edges] [edge [0 1000]])))
                         (into {} (for [edge free-edges] [edge -1])) ; Minimize currentl
                         (into {}
                               (concat
                                (for [node nodes] ;; Current conservation
                                  [(into {}
                                         (concat
                                          (for [in  (in-map node)]  [[in node]   1])
                                          (for [out (out-map node)] [[node out] -1])))
                                   [0 0]])
                                (for [[s t :as edge] (cons key-edge free-edges)] ;; I * R >= v_t - v_s
                                  [{edge 1000, s 1, t -1} [0 (when (= key-edge edge) 0)]])))))]
        (println "\n\n" key-edge "\n" sol)
        true                            ;??
        )))



;; Seems buggy in several ways; just try on 4x3 grid world.  Loses connectivity, voltages are messed up, etc.  
  (defn find-acyclic-edges
    "Take a directed edge list, list of source nodes, and list of target nodes,
   and return a list of edges that may be on an aclyic path from a source to a target.
   Uses a the above method followed by a verification based on leaving resistances unspec.
   in the above algorithm.  (If there exists an aclycic path through e, there must be a setting for 
   resistances that makes current flow through it.  This almo"
    [edge-list sources sinks]
    (filter #(edge-acyclic? edge-list % sources sinks) edge-list))

  (deftest find-acyclic-edges-simple-test
    (is (= (set (find-acyclic-edges [[:s :t] [:t :u] [:t :x]] [:s] [:u])) 
           #{[:s :t] [:t :u]}))
    (is (= (set (find-acyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t]] [:s] [:u])) 
           #{[:s :t] [:t :u]}))
    (is (= (set (find-acyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u]] [:s] [:u])) 
           #{[:s :t] [:t :u] [:t :x] [:x :u]} ))  
    (is (= (set (find-acyclic-edges [[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]] [:s] [:u]))
           #{[:s :t] [:t :u] [:t :x] [:x :t] [:x :u] [:s :x]} ))))