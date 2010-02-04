(ns edu.berkeley.ai.util.graphviz
;  (:import [java.util IdentityHashMap HashMap Map])
  (:import [java.util HashSet])
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.pdf)
  )

; nodes is a set of nodes, edges is a map from sets of edges to costs

(def *default-graphviz-dir* "/tmp/")

(defn- attribute-string [label-or-attribute-map]
  (when label-or-attribute-map
    (str "["
	 (str-join "," 
	   (map (fn [[k v]] (str (name k) "=" v))
		(if (map? label-or-attribute-map) 
		  label-or-attribute-map
		  {:label (double-quote label-or-attribute-map)})))
	 "]")))
      


(defn- walk-graph [root node-key-fn node-label-fn edge-child-pair-fn #^HashSet visited indexer]
  (let [node-key  (node-key-fn root)
	node-map (node-label-fn root)]
;    (println node-key)
;    (println node-name)
;    (println node-map)
    (when-not (.contains visited node-key)
      (.add visited node-key)
      (apply str
	     (indexer node-key) (attribute-string node-map) ";\n"
	     (apply concat 
	       (for [[edge-map child] (edge-child-pair-fn root)]
		 (cons (str (indexer node-key) " -> " (indexer (node-key-fn child)) 
			    (attribute-string edge-map)
			    ";\n")
		       (walk-graph child node-key-fn node-label-fn edge-child-pair-fn visited indexer))))))))

(defn write-graphviz
  ([roots node-key-fn node-label-fn edge-child-pair-fn] 
     (write-graphviz  
      (fresh-random-filename *default-graphviz-dir* ".dot") 
      roots node-key-fn node-label-fn edge-child-pair-fn))
  ([filename roots node-key-fn node-label-fn edge-child-pair-fn] 
     (let [pdf-file (str (file-stem filename) ".pdf")
           indexer (memoize (fn [x] (double-quote (gensym))))
           vis      (HashSet.)]
       (spit filename
	 (str "strict digraph {\n"
	      " rankdir = LR;\n"
;	      " rotate=90;\n"
	      (apply str (for [root roots] (walk-graph root node-key-fn node-label-fn edge-child-pair-fn vis indexer)))
	      "}\n"))
       (sh "dot" "-Tpdf" "-o" pdf-file filename)
       pdf-file)))

(defn graphviz 
  ([root node-key-fn node-label-fn edge-child-pair-fn] 
     (show-pdf-page (prln (write-graphviz [root] node-key-fn node-label-fn edge-child-pair-fn))))
  ([filename root node-key-fn node-label-fn edge-child-pair-fn] 
     (show-pdf-page (prln (write-graphviz filename [root] node-key-fn node-label-fn edge-child-pair-fn)))))

(defn graphviz-el
  "Draw a graph given an edge list, and optional node label map."
  ([el] (graphviz-el el {}))
  ([el nl]
     (let [em (map-vals #(map second %) (unsorted-group-by first el))]
       (show-pdf-page 
        (prln 
         (write-graphviz 
          (set (concat (keys nl) (apply concat el)))
;          (or (seq (clojure.set/difference (set (concat (keys nl) (apply concat el))) (set (map second el))))
;              [(first (first el))])
          identity #(get nl % %) #(for [e (get em %)] [nil e])))))))

; (graphviz 0 identity str (fn [i] (into {} (for [j (range (inc i) (min 10 (+ i 3)))] [j j]))))

; http://www.graphviz.org/Documentation.php	  
; http://www.graphviz.org/doc/info/lang.html
; http://www.graphviz.org/doc/info/attrs.html#dd:orientation
  
; http://www.dynagraph.org/documents/dynagraph.html  

  
  

       
  
  

