(ns exp.causal-graphs
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util [pdf :as pdf] [graphviz :as gv]]
            [vijual.graphical :as vg]
            )
  )

(defn show-directed-graph 
  "Take a list of [src dst] pairs and draw the graph on the screen."
  ( [dg] (pdf/show-image (vg/draw-directed-graph-image dg)))
  ( [dg ni] (pdf/show-image (vg/draw-directed-graph-image dg ni))))

(defn group 
  "Take a flattened representation of a 2-d seq, and return the 2-d seq"
  [num-fn s]
  (loop [s s, result []]
    (if (empty? s) result
      (let [n (num-fn (first s))]
        (recur (drop (inc n) s)
               (conj result (take n (next s))))))))

(defn read-causal-graph
  "Read a causal graph from FD/LAMA preprocessing stage"
  [filename]
  (apply concat
    (for [[i ls] (util/indexed
                  (group first 
                    (map #(read-string (str "[" % "]"))
                      (next (take-while #(not (= % "end_CG")) 
                              (drop-while #(not (= % "begin_CG"))
                                (.split #^String (slurp filename) "\n")))))))]
      (cons [i i]
       (for [[j _] ls] [i j])))))

(import '[java.util HashSet Stack HashMap])
(defn scc-graph 
  "Take an edge list and return [edge-list node-set-map] for graph of sccs.
   Every node must have at least one outgoing edge (incl. self loop) or will be skipped."
  [edges]
  (let [pe (util/map-vals #(map second %) (util/group-by first edges))
        e  (HashMap. pe)
        re (HashMap. (util/map-vals #(map first %) (util/group-by second edges)))
        s (Stack.)]
    (while (not (.isEmpty e))
     ((fn dfs1 [n]
        (when (.containsKey e n) 
          (let [nns (.get e n)]
            (.remove e n)
            (doseq [nn nns] (dfs1 nn)))
          (.push s n)))
      (first (keys e))))
    (let [sccs (into {} 
                 (util/indexed
                  (remove empty?
                          (for [n (reverse (seq s))]
                            ((fn dfs2 [n]
                               (when (.containsKey re n)
                                 (let [nns (.get re n)]
                                   (.remove re n)              
                                   (cons n (apply concat (map dfs2 nns))))))
                             n)))))
          rev-sccs (into {} (for [[k vs] sccs, v vs] [v k]))]
      [(distinct 
         (for [[scc nodes] sccs
               node nodes
               outgoing (get pe node)]
           [scc (get rev-sccs outgoing)]))
       sccs])))

(defn map-ize [key-fn s]
  (into {}
    (loop [s s, result nil]
      (if (empty? s) result
        (let [[k & r] s
              [vs r]  (split-with (complement key-fn) r)]
;          (println vs)
          (assert (key-fn k))
          (recur r (cons [ (key-fn k) vs] result)))))))

(defn read-groups
  "Read a groups file from LAMA and output a map from variable names to atoms."
  [file]
  (map-ize #(when-not (.startsWith #^String % " ") (.substring #^String % 0 (dec (count %))))
           (.split #^String (slurp file) "\n")))

(defn read-var-ordering [preproc-filename]
  (vec
   (map #(first (.split #^String % " "))
    (drop 2
     (take-while #(not (= % "end_variables")) 
      (drop-while #(not (= % "begin_variables"))
       (.split #^String (slurp preproc-filename) "\n")))))))

(defn read-ordered-groups
  [groups-file preproc-file]
  (let [m (read-groups groups-file)
        o (read-var-ordering preproc-file)]
    (vec (map #(util/safe-get m %) o)))) 

(def *working-dir* "/tmp/")
(def *lama-dir* "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/")

(defn lama-translate [stem]
  (util/sh (str *lama-dir* "translate/translate.py") (str stem "-domain.pddl") (str stem ".pddl")
           :dir *working-dir*))

(defn lama-preprocess []
  (util/sh (str *lama-dir* "preprocess/preprocess")
           :in (slurp (str *working-dir* "output.sas"))
           :dir *working-dir*))


(defn causal-graph-info [cg]
  (gv/graphviz-el cg)
  (let [cg (scc-graph cg)]
;    (println cg "\n\n" (sinkize cg))
    (gv/graphviz-el cg)
    cg))

(defn pddl-causal-graph-info [stem]
  (println (lama-translate stem))
  (println (lama-preprocess))  
  (causal-graph-info (read-causal-graph (str *working-dir* "output"))))




; (show-directed-graph (read-causal-graph  "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/output"))

; (doseq [ [i g]  (indexed (read-ordered-groups  "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/test.groups" "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/output")) ] (println i "\n" g))