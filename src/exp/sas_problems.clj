(ns exp.sas-problems
  (:require [exp [sas :as sas] [taxi :as taxi]]))



(defn sas-sample-files [n]
  (into {}
    (concat  
      [["2x2-taxi"  (taxi/write-taxi-strips (taxi/make-random-taxi-env 2 2 2 1))]]
      (for [domain ["elevators" "openstacks" "parcprinter" "pegsol" "scanalyzer" #_ "sokoban" "transport" "woodworking"]]
        [(str "IPC6-" domain)
         (str "/Users/jawolfe/Projects/research/IPC/ipc2008-no-cybersec/seq-opt/" domain "-strips/p"
              (if (< n 10) (str "0" n) (str n)))]))
    
        )
  )


