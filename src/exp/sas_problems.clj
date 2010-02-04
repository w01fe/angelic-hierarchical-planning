(ns exp.sas-problems
  (:require [exp [sas :as sas] [taxi :as taxi] [taxi-infinite :as taxi-infinite]]))

(defn dig2 [n]
  (assert (< 0 n 100))
  (if (< n 10) (str "0" n) (str n)))

(def ipc1-dir "/Users/jawolfe/Projects/research/IPC/IPC1/")
(def ipc1-problems 
  (into {}
    (concat
     (for [[dom n p] [["gripper" 20 "strips/"] ["logistics" 30 "strips/"] ["mystery" 30 "strips/"]
                      ; ["movie" 30 "strips/"] ["mprime" 30 "strips/"] ; movie uses c.e., mprime bugyg
                      ]]
       [(str "IPC1-ROUND1-" dom)
        (for [i (range 1 (inc n))]
          (delay (sas/make-sas-problem-from-pddl
                  (str ipc1-dir "domains/" dom "-strips.pddl")
                  (str ipc1-dir "round1/" dom "/" p "prob" (dig2 n) ".pddl"))))])
     (for [[dom n] [["grid" 5] ["logistics" 5] #_ ["mprime" 5]]]
       [(str "IPC1-ROUND2-" dom)
        (for [i (range 1 (inc n))]
          (delay (sas/make-sas-problem-from-pddl
                  (str ipc1-dir "domains/" dom "-strips.pddl")
                  (str ipc1-dir "round2/" dom "/" "prob" (dig2 n) ".pddl"))))]))))

(defn sas-sample-files [n]
  (into {}
    (concat  
      [["2x2-taxi"  (taxi/write-taxi-strips (taxi/make-random-taxi-env 2 2 2 1))]]
      (for [domain ["elevators" "openstacks" "parcprinter" "pegsol" "scanalyzer" #_ "sokoban" "transport" "woodworking"]]
        [(str "IPC6-" domain)
         (str "/Users/jawolfe/Projects/research/IPC/ipc2008-no-cybersec/seq-opt/" domain "-strips/p"
              (dig2 n))]))
    
        )
  )


