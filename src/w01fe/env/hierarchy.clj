(ns exp.hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env]
            ))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol HighLevelAction
  (immediate-refinements- [a s])
  (cycle-level- [a s]))

(def *ref-counter* (util/sref 0))
(def *plan-counter* (util/sref 0))

(defn reset-ref-counter [] 
  (util/sref-set! *ref-counter* 0)
  (util/sref-set! *plan-counter* 0))


;;; Consumers should use these functions, rather than raw functions. 


;; TODO: this forces eagerness, may not be desirable in some situations.
(defn immediate-refinements [a s]  
  ;(println "Refs for " (env/action-name a) "from" (map #(env/get-var s %) '[[atx] [aty]]))
  (util/timeout)
  (let [refs (immediate-refinements- a s)]
    (util/print-debug 3 "\nRefs for " (env/action-name a) "from" (env/as-map s) "are" 
             (apply str (doall (map #(str "\n  " (util/str-join ", " (map env/action-name %))) refs))))
    (util/sref-set! *ref-counter*  (+ 1            (util/sref-get *ref-counter*)))
    (util/sref-set! *plan-counter* (+ (count refs) (util/sref-get *plan-counter*)))
    refs))

(defn cycle-level [a s]
  (when-not (env/primitive? a)
    (cycle-level- a s)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchical Envs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol HierarchicalEnv (env [h]) (initial-plan [h]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn run-counted [f]
  (env/reset-next-counter)
  (reset-ref-counter)
  [(f) (util/sref-get env/*next-counter*) (util/sref-get env/*optimistic-counter*) (util/sref-get env/*pessimistic-counter*) (util/sref-get *ref-counter*) (util/sref-get *plan-counter*)])

