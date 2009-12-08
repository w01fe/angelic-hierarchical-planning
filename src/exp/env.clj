(ns exp.env
  (:require [edu.berkeley.ai.util :as util])
  )



(defprotocol FactoredState
  (set-var [state var val])
  (get-var [state var])
  (list-vars [state])
  (as-map [state]))


(extend clojure.lang.IPersistentMap
  FactoredState {:set-var assoc :get-var util/safe-get :list-vars keys :as-map identity})

(extend clojure.lang.PersistentHashMap$TransientHashMap
  FactoredState {:set-var assoc! :get-var util/safe-get :list-vars keys :as-map persistent!})

(defn state-matches-map? [fs m]
  (every? (fn [[k v]] (= (get-var fs k) v)) m))

;; TODO: make method so we can use transients?
(defn apply-effects [fs m]
  (reduce (fn [s [k v]] (set-var s k v)) fs m))


(defprotocol Action
  (action-name [a]))

(defprotocol PrimitiveAction
  (applicable? [a s])
  (next-state-and-reward  [a s])
  )

(defprotocol ContextualAction
  (precondition-context [a]))

(deftype FactoredPrimitive [name precond-map effect-map reward] 
  [Action PrimitiveAction ContextualAction]
  (action-name [a] name)
  (applicable? [a s]
    (every? (fn [[var val]] (= (get-var s var) val)) precond-map))
  (next-state-and-reward  [a s]
    [(apply-effects s effect-map) reward])
  (precondition-context [a]
    (keys precond-map)))

(defmethod print-method ::FactoredPrimitive [a o] (print-method (action-name a) o))


(def *next-counter* (util/sref 0))

;(import '[java.util HashMap])
;(def *next-ba* (HashMap.))

(defn reset-next-counter [] 
  (util/sref-set! *next-counter* 0)
;  (def *next-ba* (HashMap.))
  )

 

;; TODO: it feels clunky for this to live outside 

(defn successor [action state]
;  (prn "next" (:name action))
  (assert (applicable? action state))
  (util/sref-set! *next-counter* (inc (util/sref-get *next-counter*)))
 ; (.put #^HashMap *next-ba* (action-name action) (inc (get *next-ba* (action-name action) 0)))
  (let [[next reward] (next-state-and-reward action state)]
    [(vary-meta next assoc
       :act-seq (conj (or (:act-seq ^state) []) action)
       :reward (+ reward (or (:reward ^state) 0)))
     reward]))



(defn solution-and-reward [state]
  (let [{:keys [act-seq reward]} ^state]
    [(or act-seq []) (or reward 0)]))

(defn reward [state]
  (or (:reward ^state) 0))

;; Environments have a single goal state
;; Goal fn returns [sol reward] or nil.

(defprotocol Env
  (initial-state [env])
  (actions-fn    [env])
  (goal-fn      [env]))

(defprotocol FactoredEnv
  (goal-map [env]))

(defn make-finish-action [env]
  (FactoredPrimitive 
    '[finish]
    (goal-map env)
    (zipmap (keys (initial-state env)) (repeat :goal))
    0))

(defn make-finish-goal-state [env]
  (zipmap (keys (initial-state env) (repeat :goal))))


;;; Useful logging state


(deftype LoggingFactoredState [init] [FactoredState]
  (get-var [state var]
   (swap! (:gets (meta state)) conj var)
   (if-let [[_ val] (find (:puts (meta state)) var)]
       val
     (get-var init var)))
  (set-var [state var val]
;   (util/assert-is (get-var init var)) ; can't do this since val might be nil ...
    (LoggingFactoredState. init 
      {:gets (atom @(:gets (meta state))) 
       :puts (assoc (:puts (meta state)) var val)}
      {}))
  (list-vars [state] (list-vars init))
  (as-map [state] (merge (as-map init) (:puts (meta state)))))

(defn wrap-logging-state [init-state] (LoggingFactoredState init-state {:gets (atom #{}) :puts {}} {}))
(defn get-logging-state-gets [s] @(:gets (meta s)))
(defn get-logging-state-puts [s] (util/safe-get (meta s) :puts))
