(ns angelic.util.cluster
  (:require [angelic.util :as util] 
	    [angelic.util.experiments :as experiments]))

(def *default-clj* (util/base-local "scripts/clj"))

(def *default-qsub-options*
     ["-r" "n" 
      "-M" "jawolfe@berkeley.edu"
      "-q" "zen"
      "-l" "nodes=1:ppn=1:cpu3000"
      "-l" "mem=1200m"
      "-l" "walltime=24:00:00"])

(defn run-files-subprocesses [files]
  (doseq [f files]
    (util/sh *default-clj* f)))

(defn run-files-cluster 
  ([files]      (run-files-cluster "jawolfe" files))
  ([name files]
     (println "---- submitting" name)
     (doseq [f files]
       (println
        (apply util/sh 
               (concat ["qsub"
                        "-N" name 
                        "-o" (str (util/file-stem f) ".out")
                        "-e" (str (util/file-stem f) ".err")]
                       *default-qsub-options*
                       [:in (str "java -server -Xmx1024m -cp " (System/getProperty "java.class.path") " clojure.main " f) :dir (util/dirname f)]))))))

(defn run-experiment-set-subprocesses [es]
  (run-files-subprocesses 
   (experiments/write-experiment-set es)))

(defn run-experiment-set-cluster 
  ([es] (run-experiment-set-cluster es 0 (count es)))
  ([es min max]
     (run-files-cluster 
      (:name (first es))
      (experiments/write-experiment-set es min max))))

(defn cluster-smart-runner [job-map & [continue? run-dir]]
  (experiments/smart-runner
   job-map
   (fn [name file] (run-files-cluster name [file]))
   continue? run-dir))


;(defn run-in-subprocess [filename forms] 
;  (spit filename (util/str-join "\n" forms))
;  (util/sh *default-clj* filename))
