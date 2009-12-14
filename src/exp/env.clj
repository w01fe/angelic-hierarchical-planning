(ns exp.env
  (:require [edu.berkeley.ai.util :as util])
  )


(defprotocol ContextualState
  (current-context [s])
  (extract-context [s c])
  (apply-effects [s e])
  (get-logger [s])  
  )

;; For now, we pass in precondition context to help with integration -- should be ignored eventually!
(defprotocol LoggingState
  (extract-effects [s c]))

(defprotocol FactoredState
  (set-var [state var val])
  (get-var [state var])
  (list-vars [state])
  (as-map [state]))

(defn apply-factored-effects [fs m]
  (reduce (fn [s [k v]] (set-var s k v)) fs m))

(declare make-logging-factored-state)

(deftype LoggingFactoredState [init] :as state
  FactoredState
   (get-var [var]
     (swap! (:gets (meta state)) conj var)
     (get-var init var))
   (set-var [var val]
;     (println "setting" var "to " val)
     (LoggingFactoredState. (set-var init var val)  ; init
                            {:gets (atom @(:gets (meta state))) 
                             :puts (assoc (:puts (meta state)) var val)}
                            {}))
   (list-vars [] (list-vars init))
   (as-map [] init)
  LoggingState
   (extract-effects [c] (util/safe-get (meta state) :puts))
  ContextualState 
   (current-context [] (keys init))
   (extract-context [c] (select-keys init c))
   (apply-effects   [e] (apply-factored-effects state e))
   (get-logger      [] (make-logging-factored-state init)))

(defn make-logging-factored-state [init-state] 
  (LoggingFactoredState init-state {:gets (atom #{}) :puts {}} {}))


(def *m1* {:set-var assoc :get-var util/safe-get :list-vars keys :as-map identity})
(def *m2* {:current-context keys :extract-context select-keys 
                   :apply-effects merge :get-logger make-logging-factored-state})
(def *m3* {:set-var assoc! :get-var util/safe-get :list-vars keys :as-map persistent!})


(extend clojure.lang.PersistentHashMap FactoredState *m1*  ContextualState *m2*)
(extend clojure.lang.PersistentArrayMap FactoredState *m1*  ContextualState *m2*)
 
(extend clojure.lang.PersistentHashMap$TransientHashMap
  FactoredState *m3* ContextualState *m2*)
(extend clojure.lang.PersistentArrayMap$TransientArrayMap
  FactoredState *m3* ContextualState *m2*)

(defn state-matches-map? [fs m]
  (every? (fn [[k v]] (= (get-var fs k) v)) m))

;; TODO: make method so we can use transients?





(defn get-logging-state-gets [s] @(:gets (meta s)))
(defn get-logging-state-puts [s] (util/safe-get (meta s) :puts))




(defprotocol Action
  (primitive? [a])
  (action-name [a]))

(defprotocol PrimitiveAction
  (applicable? [a s])
  (next-state-and-reward  [a s])
  )

(defprotocol ContextualAction
  (precondition-context [a s]))

(deftype FactoredPrimitive [name precond-map effect-map reward] 
  Action 
    (action-name [] name)
    (primitive? [] true)
  PrimitiveAction 
    (applicable? [s]
      (every? (fn [[var val]] (= (get-var s var) val)) precond-map))
    (next-state-and-reward [s]
      [(apply-effects s effect-map) reward])
  ContextualAction
    (precondition-context [s]
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
  (util/timeout)
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
    (zipmap (list-vars (initial-state env)) (repeat :goal))
    0))

(defn make-finish-goal-state [env]
  (zipmap (list-vars (initial-state env)) (repeat :goal)))




