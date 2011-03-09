(ns angelic.hierarchy
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]
            angelic.env.util
))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Counters ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *optimistic-counter* (util/sref 0))
(def *pessimistic-counter* (util/sref 0))
(def *ref-counter* (util/sref 0))
(def *plan-counter* (util/sref 0))

(defn reset-ref-counter [] 
 (util/sref-set! *optimistic-counter* 0)
 (util/sref-set! *pessimistic-counter* 0)
 (util/sref-set! *ref-counter* 0)
 (util/sref-set! *plan-counter* 0))

			
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol HighLevelAction
  (immediate-refinements- [a s])
  (cycle-level- [a s]))

;;; Consumers should use these functions, rather than raw functions. 

;; TODO: this forces eagerness, may not be desirable in some situations.
(defn immediate-refinements [a s]  
  ;(println "Refs for " (env/action-name a) "from" (map #(state/get-var s %) '[[atx] [aty]]))
  (util/timeout)
  (let [refs (immediate-refinements- a s)]
    (util/print-debug 3 "\nRefs for " (env/action-name a) "from" (state/as-map s) "are" 
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
  [(f)
   (util/sref-get env/*next-counter*)
   (util/sref-get *optimistic-counter*)
   (util/sref-get *pessimistic-counter*)
   (util/sref-get *ref-counter*)
   (util/sref-get *plan-counter*)])




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; Generalized Goal Actions ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stuff for generalized-goal actions.  Perhaps roll into protocol later.
; Idea here is:
 ; for actions A whose refinements are all [b A] or []. 
 ; assume different As with same name will behave same, except different goals.
 ; Goal must always be on same set of vars.
(defmulti gg-action type)
(defmethod gg-action :default [x] nil)
