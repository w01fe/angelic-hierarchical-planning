(ns w01fe.env
  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util])
  (:import [java.util Set Map])
  )


(defprotocol Action
  (primitive? [a])
  (action-name [a]))

(defprotocol PrimitiveAction
  (applicable? [a s])
  (next-state-and-reward  [a s]) ; Precondition: applicable.
  )

(defprotocol ContextualAction
  (precondition-context [a s]))


(def *next-counter* (util/sref 0))

(defn reset-next-counter [] 
  (util/sref-set! *next-counter* 0))

 

;; TODO: it feels clunky for this to live outside 

(defn successor [action state]
;  (prn "next" (:name action))
  (util/timeout)
  (assert (applicable? action state))
  (util/print-debug 4 "Progressing" action #_ state)
  (util/sref-set! *next-counter* (inc (util/sref-get *next-counter*)))
 ; (.put #^HashMap *next-ba* (action-name action) (inc (get *next-ba* (action-name action) 0)))
  (let [[next reward] (next-state-and-reward action state)
        old-meta      (meta state)]
    [(vary-meta next assoc
       :act-seq (cons (action-name action) (:act-seq old-meta))
                                        ;(conj (or (:act-seq (meta state)) []) action)
       :reward (+ reward (or (:reward old-meta) 0)))
     reward]))


(defn solution-and-reward [state]
  (let [{:keys [act-seq reward]} (meta state)]
    [(reverse act-seq) (or reward 0)]))

(defn reward [state]
  (or (:reward (meta state)) 0))

;; Environments have a single goal state
;; Goal fn returns [sol reward] or nil.

(defprotocol Env
  (initial-state [env])
  (actions-fn    [env])
  (goal-fn      [env]))

(defprotocol FactoredEnv
  (goal-map [env]))


(defn initial-logging-state [env]
  (let [init (initial-state env)]
    (get-logger init (current-context init))))



