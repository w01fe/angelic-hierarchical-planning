(ns edu.berkeley.ai.util.graphviz
;  (:import [java.util IdentityHashMap HashMap Map])
  (:import [java.util HashSet])
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.pdf)
  )

; nodes is a set of nodes, edges is a map from sets of edges to costs

(def *default-graphviz-dir* "/tmp/")

(defn- walk-graph [root node-name-fn child-map-fn #^HashSet visited]
  (let [node-name (node-name-fn root)]
    (when-not (.contains visited node-name)
      (.add visited node-name)
      (apply str
	     (double-quote node-name) ";\n"
	     (apply concat 
	       (for [[edge-name child] (child-map-fn root)]
		 (cons (str (double-quote node-name) " -> " (double-quote (node-name-fn child)) ";\n")
		       (walk-graph child node-name-fn child-map-fn visited))))))))

(defn write-graphviz
;  ([root node-name-fn child-map-fn] 
;     (write-graphviz root node-name-fn child-map-fn true))
  ([root node-name-fn child-map-fn] 
     (write-graphviz  (fresh-random-filename *default-graphviz-dir* ".dot") root node-name-fn child-map-fn))
  ([filename root node-name-fn child-map-fn]
     (let [pdf-file (str (file-stem filename) ".pdf")]
       (spit filename
	 (str "strict digraph {\n"
	      " rankdir = LR;\n"
;	      " rotate=90;\n"
	      (walk-graph root node-name-fn child-map-fn (HashSet.))
	      "}\n"))
       (sh "dot" "-Tpdf" "-o" pdf-file filename)
       pdf-file)))

(defn graphviz [& args] (show-pdf-page (prln (apply write-graphviz args))))

; http://www.graphviz.org/Documentation.php	  
; http://www.graphviz.org/doc/info/lang.html
; http://www.graphviz.org/doc/info/attrs.html#dd:orientation
  
; http://www.dynagraph.org/documents/dynagraph.html  

  
  

       
  
  

