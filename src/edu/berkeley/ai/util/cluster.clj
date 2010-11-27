(ns edu.berkeley.ai.util.cluster
  (:require [edu.berkeley.ai [util :as util]]
	    [edu.berkeley.ai.util.experiments :as experiments]))

(def *default-clj* (util/base-local "scripts/clj"))

(def *default-qsub-options*
     ["-r" "n" 
      "-M" "jawolfe@berkeley.edu"
      "-q" "batch"
      "-l" "nodes=1:ppn=1:cpu3000"
      "-l" "mem=1200m"
      "-l" "walltime=24:00:00"])

(defn run-files-subprocesses [files]
  (doseq [f files]
    (util/sh *default-clj* f)))

(defn run-files-cluster 
  ([files]      (run-files-cluster "jawolfe" files))
  ([name files]
     (println name)
     (doseq [f files]
       (println 
	(apply util/sh 
               (util/prln (concat ["qsub"
                  "-q" "zen"                 
		  "-N" name 
		  "-o" (str (util/file-stem f) ".out")
		  "-e" (str (util/file-stem f) ".err")]
		*default-qsub-options*
		[:in (str "java -server -Xmx1024m -cp " user/*classpath* " clojure.main " f) :dir (util/dirname f)])))))))

(defn run-experiment-set-subprocesses [es]
  (run-files-subprocesses 
   (experiments/write-experiment-set es)))

(defn run-experiment-set-cluster 
  ([es] (run-experiment-set-cluster es 0 (count es)))
  ([es min max]
     (run-files-cluster 
      (:name (first es))
      (experiments/write-experiment-set es min max))))

;(defn run-in-subprocess [filename forms] 
;  (spit filename (util/str-join "\n" forms))
;  (util/sh *default-clj* filename))


