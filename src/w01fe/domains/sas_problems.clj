(ns exp.sas-problems
  (:require [exp [sas :as sas] [taxi :as taxi] [taxi-infinite :as taxi-infinite]])
  (:use [edu.berkeley.ai [util :as util]])
  (:import [java.io File])
  )

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
                  (str ipc1-dir "round1/" dom "/" p "prob" (dig2 i) ".pddl"))))])
     (for [[dom n] [["grid" 5] ["logistics" 5] #_ ["mprime" 5]]]
       [(str "IPC1-ROUND2-" dom)
        (for [i (range 1 (inc n))]
          (delay (sas/make-sas-problem-from-pddl
                  (str ipc1-dir "domains/" dom "-strips.pddl")
                  (str ipc1-dir "round2/" dom "/" "prob" (dig2 i) ".pddl"))))]))))

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

(defn funky-sort [strs]
  (sort (comparator (fn [#^String s1, #^String s2] (or (< (count s1) (count s2)) (and (= (count s1) (count s2)) (< (compare s1 s2) 0))))) strs))

(def ipc2-dir "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Logistics/Track1/Typed/")
(def ipc2-logistics
     (for [f (funky-sort (remove #{"probLOGISTICS-11-0.pddl"} (filter #(.startsWith #^String % "probL") (seq (.list (File. ipc2-dir))))))]
       (delay (do (println f) (sas/make-sas-problem-from-pddl (str ipc2-dir "domain.pddl") (str ipc2-dir  f))))))

(def cptdir "/Users/jawolfe/Projects/research/IPC/cpt/pddl/")
(def cpt-logistics
     (for [i (range 1 10)]
       (delay (sas/make-sas-problem-from-pddl 
               (str cptdir "domain-logistics.pddl")
               (str cptdir "logistics0" i ".pddl")))))

(def cpt-logistics2
     (for [i (range 1 41)]
       (delay (sas/make-sas-problem-from-pddl 
               (str cptdir "domain-logisticsaips.pddl")
               (str cptdir "logisticsaips" (dig2 i) ".pddl")))))