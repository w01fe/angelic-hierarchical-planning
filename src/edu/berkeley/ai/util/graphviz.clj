(ns edu.berkeley.ai.util.graphviz
;  (:import [java.util IdentityHashMap HashMap Map])
  (:import [java.util HashSet])
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.pdf)
  )

; nodes is a set of nodes, edges is a map from sets of edges to costs

(def *default-graphviz-dir* "/tmp/")

(defn- walk-graph [root node-key-fn node-label-fn edge-child-pair-fn #^HashSet visited indexer]
  (let [node-key  (node-key-fn root)
	node-name (node-label-fn root)]
;    (println node-name)
    (when-not (.contains visited node-key)
      (.add visited node-key)
      (apply str
	     (indexer node-key) "[label=" (double-quote node-name) "]" ";\n"
	     (apply concat 
	       (for [[edge-name child] (edge-child-pair-fn root)]
		 (cons (str (indexer node-key) " -> " (indexer (node-key-fn child)) 
			    (when edge-name (str " [label=" (double-quote edge-name) "]"))
			    ";\n")
		       (walk-graph child node-key-fn node-label-fn edge-child-pair-fn visited indexer))))))))

(defn write-graphviz
  ([root node-key-fn node-label-fn edge-child-pair-fn] 
     (write-graphviz  
      (fresh-random-filename *default-graphviz-dir* ".dot") 
      root node-key-fn node-label-fn edge-child-pair-fn))
  ([filename root node-key-fn node-label-fn edge-child-pair-fn] 
     (let [pdf-file (str (file-stem filename) ".pdf")]
       (spit filename
	 (str "strict digraph {\n"
	      " rankdir = LR;\n"
;	      " rotate=90;\n"
	      (walk-graph root node-key-fn node-label-fn edge-child-pair-fn 
			  (HashSet.) (memoize (fn [x] (double-quote (gensym)))))
	      "}\n"))
       (sh "dot" "-Tpdf" "-o" pdf-file filename)
       pdf-file)))

(defn graphviz [& args] (show-pdf-page (prln (apply write-graphviz args))))


; (graphviz 0 identity str (fn [i] (into {} (for [j (range (inc i) (min 10 (+ i 3)))] [j j]))))

; http://www.graphviz.org/Documentation.php	  
; http://www.graphviz.org/doc/info/lang.html
; http://www.graphviz.org/doc/info/attrs.html#dd:orientation
  
; http://www.dynagraph.org/documents/dynagraph.html  

  
  

       
  
  

