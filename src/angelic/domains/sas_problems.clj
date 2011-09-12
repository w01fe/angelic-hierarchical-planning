(ns angelic.domains.sas-problems
  (:require [angelic.util :as util] 
            [angelic.sas :as sas]
            [angelic.domains.taxi :as taxi]
            [angelic.domains.taxi-infinite :as taxi-infinite])
  (:import [java.io File]))


(defn dig2 [n]
  (assert (< 0 n 100))
  (if (< n 10) (str "0" n) (str n)))

(def ipc1-dir "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/IPC1/")
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
      ;     [["2x2-taxi"  (taxi/write-taxi-strips (taxi/make-random-taxi-env 2 2 2 1))]]
      (for [domain ["elevators" "openstacks" "parcprinter" "pegsol" "scanalyzer" #_ "sokoban" "transport" "woodworking"]]
        [(str "IPC6-" domain)
         (str "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/ipc2008-no-cybersec/seq-opt/" domain "-strips/p"
              (dig2 n))]))
    
        )
  )

(defn sas-sample-problem [f]
  (sas/make-sas-problem-from-pddl (str f "-domain.pddl") (str f ".pddl")))

(defn funky-sort [strs]
  (sort (comparator (fn [^String s1, ^String s2] (or (< (count s1) (count s2)) (and (= (count s1) (count s2)) (< (compare s1 s2) 0))))) strs))


(def ipc2-dir "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Logistics/Track1/Typed/")
(def direct-ipc2-logistics
     (for [f (funky-sort (remove #{"probLOGISTICS-11-0.pddl"} (filter #(.startsWith ^String % "probL") (seq (.list (File. ipc2-dir))))))]
       (delay (do (println f) (sas/make-sas-problem-from-pddl (str ipc2-dir "domain.pddl") (str ipc2-dir  f))))))

(def ipc2-logistics-names
     (for [f (funky-sort (remove #{"probLOGISTICS-11-0.pddl"} (filter #(.startsWith ^String % "probL") (seq (.list (File. ipc2-dir))))))]
       f))

(def ipc2-logistics-dir (util/base-local "problems/logistics/"))

(defn translate-ipc2-logistics []
  (doseq [[i f] (util/indexed (funky-sort (remove #{"probLOGISTICS-11-0.pddl"} (filter #(.startsWith ^String % "probL") (seq (.list (File. ipc2-dir)))))))]
    (println f)
    (sas/lama-translate-to (str ipc2-dir "domain.pddl") (str ipc2-dir  f) (str ipc2-logistics-dir i))))

(def ipc2-logistics
  (for [i (range 27)]
    (delay (sas/make-sas-problem-from-lama (str ipc2-logistics-dir i ".groups") (str ipc2-logistics-dir i ".sas")))))



(def ipc2-miconic-src-dir "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Elevator/m10-strips/")

(def ipc2-miconic-names
     (for [i (range 1 31) j (range 5)] (str i "-" j)))

(def ipc2-miconic-dir (util/base-local "problems/miconic/"))

(def ipc2-miconic
  (for [n ipc2-miconic-names]
    (delay (sas/make-sas-problem-from-pddl (str ipc2-miconic-src-dir "domain.pddl") (str ipc2-miconic-src-dir "s" n ".pddl")))))


(defn translate-ipc2-miconic []
  (doseq [n ipc2-miconic-names]
    (println n)
    (sas/lama-translate-to (str ipc2-miconic-src-dir "domain.pddl") (str ipc2-miconic-src-dir "s" n ".pddl") (str ipc2-miconic-dir n))))

(def ipc2-miconic-pp
  (for [n ipc2-miconic-names]
    (delay (sas/make-sas-problem-from-lama (str ipc2-miconic-dir n ".groups") (str ipc2-miconic-dir n ".sas")))))





(def cptdir "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/cpt/pddl/")
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


(def ipc3-depots-dir "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/IPC3/Tests1/Depots/Strips/")

(def ipc3-depots
  (for [i (range 1 23)]
    (delay (sas/make-sas-problem-from-pddl
            (str ipc3-depots-dir "Depots.pddl")
            (str ipc3-depots-dir "pfile" i)))))



(def sas-sample-problems
 (memoize (fn [n]
            (concat
             [["IPC3-depots" @(nth ipc3-depots n)]
              ["IPC2-logistics" @(nth ipc2-logistics n)]
              ["IPC2-miconic" @(nth ipc2-miconic n)]]
             (for [d ["gripper" "mystery" "grid"]]
               (let [[nm ps] (first (filter #(.contains ^String (first %) ^String d) ipc1-problems))]
                 [nm @(nth ps n)]))
             (util/map-vals sas-sample-problem (sas-sample-files (inc n)))))))

