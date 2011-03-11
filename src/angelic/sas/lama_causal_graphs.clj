(ns angelic.sas.lama-causal-graphs
  (:require [angelic.util :as util]
            [angelic.util [pdf :as pdf] [graphviz :as gv] [graphs :as graphs]]
;            [vijual.graphical :as vg]
            )
  )

;; Stuff for reading and displaying causal graphs from LAMA output.

(comment
  (defn show-directed-graph 
   "Take a list of [src dst] pairs and draw the graph on the screen."
   ( [dg] (pdf/show-image (vg/draw-directed-graph-image dg)))
   ( [dg ni] (pdf/show-image (vg/draw-directed-graph-image dg ni)))))

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
                                (.split ^String (slurp filename) "\n")))))))]
      (cons [i i]
       (for [[j _] ls] [i j])))))


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
  (map-ize #(when-not (.startsWith ^String % " ") (.substring ^String % 0 (dec (count %))))
           (.split ^String (slurp file) "\n")))

(defn read-var-ordering [preproc-filename]
  (vec
   (map #(first (.split ^String % " "))
    (drop 2
     (take-while #(not (= % "end_variables")) 
      (drop-while #(not (= % "begin_variables"))
       (.split ^String (slurp preproc-filename) "\n")))))))

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
  (let [cg (graphs/scc-graph cg)]
;    (println cg "\n\n" (sinkize cg))
    (gv/graphviz-el cg)
    cg))

(defn pddl-causal-graph-info [stem]
  (println (lama-translate stem))
  (println (lama-preprocess))  
  (causal-graph-info (read-causal-graph (str *working-dir* "output"))))




; (show-directed-graph (read-causal-graph  "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/output"))

; (doseq [ [i g]  (indexed (read-ordered-groups  "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/test.groups" "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/output")) ] (println i "\n" g))