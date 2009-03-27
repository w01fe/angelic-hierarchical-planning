(ns edu.berkeley.ai.scripts.cluster
  (:require [edu.berkeley.ai [util :as util]]
	    [edu.berkeley.ai.scripts.experiments :as experiments]))

(def *default-clj* (util/base-local "scripts/clj"))
(def *default-run-dir* (util/base-local "runs/"))

(def *default-qsub-options*
     ["-r" "n" 
      "-M" "jawolfe@berkeley.edu"
      "-q" "batch"
      "-l" "nodes=1,ppn=1,cpu3000,mem=1200m"])

(defn run-files-subprocesses [files]
  (doseq [f files]
    (util/sh *default-clj* f)))

(defn run-files-cluster 
  ([files]      (run-files-cluster "jawolfe" files))
  ([name files]
     (doseq [f files]
       (apply util/sh 
	(concat ["qsub" "-N" name]
		*default-qsub-options*
		[:in (str *default-clj* f)])))))

(defn run-experiment-set-subprocesses [es]
  (run-files-subprocesses 
   (experiments/write-experiment-set es *default-run-dir*)))

(defn run-experiment-set-cluster [es]
  (run-files-cluster 
   (:name es)
   (experiments/write-experiment-set es *default-run-dir*)))

;(defn run-in-subprocess [filename forms] 
;  (util/spit filename (util/str-join "\n" forms))
;  (util/sh *default-clj* filename))


