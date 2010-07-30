(ns w01fe.hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [w01fe.env :as env]
            ))


			;; TODO: better to have single map from state to range ?
			(def *optimistic-counter* (util/sref 0))
			(def *pessimistic-counter* (util/sref 0))
			(defprotocol AngelicAction
			  (optimistic-map- [a s])
			  (pessimistic-map- [a s]))

			(defn optimistic-map [a s]
			  (util/sref-set! *optimistic-counter* (inc (util/sref-get *optimistic-counter*)))
			  (optimistic-map- a s))
			(defn pessimistic-map [a s]
			  (util/sref-set! *pessimistic-counter* (inc (util/sref-get *pessimistic-counter*)))
			  (pessimistic-map- a s))

			  AngelicAction
			    (optimistic-map- [s]
			      (if (applicable? this s) 
			        (let [[s r] (next-state-and-reward this s)] {s r}) 
			        {}))
			    (pessimistic-map- [s]
			      (if (applicable? this s) 
			        (let [[s r] (next-state-and-reward this s)] {s r}) 
			        {}))
			
				    (util/sref-set! *optimistic-counter* 0)
				      (util/sref-set! *pessimistic-counter* 0)
			
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

