(ns exp.env
  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util])
  (:import [java.util Set Map])
  )

; Get-logger takes a precondition context.  Its equality semantics will be based
;; on values within this context, and changes outside this context. 
;; E.g., if context is var a, it doesn't matter if value was originally 2 or we set it to 2.
;;       but, for var b outside context, it does matter.
(defprotocol ContextualState
  (current-context [s])
  (extract-context [s c])
  (apply-effects   [s e])
  (get-logger      [s c-set]))

(defprotocol LoggingState
  (ooc-effects     [s])  ; Return just out-of-context effects.
  (extract-effects [s]))

(defprotocol FactoredState
  (set-var   [state var val])
  (set-vars  [state vv-pairs])
  (get-var   [state var])
  (list-vars [state])
  (as-map    [state]))

;; TODO: use dissoc in some cases?
(defn fast-select-keys [map key-set]
  (let [mc (count map) kc (count key-set)]
    (assert (<= kc mc))
    (if (= mc kc) map
      (persistent! (reduce #(assoc! %1 %2 (get map %2)) (transient {}) key-set)))))

(declare make-logging-factored-state)

(deftype LoggingFactoredState [init #^Set context] :as state
  Object 
   (equals    [lfs]
     (and (= init (:init lfs)) (= context (:context lfs)) (= (ooc-effects state) (ooc-effects lfs))))
   (hashCode []
     (unchecked-add (int (hash init))
       (unchecked-multiply (int 13) (int (hash (ooc-effects state))))))
  FactoredState
   (get-var [var]
     (get-var init var))
   (set-var [var val]
     (LoggingFactoredState. (set-var init var val)  ; init
                            context
                            {:puts (assoc (:puts (meta state)) var val)}
                            {}))
   (set-vars [vv-pairs]
     (LoggingFactoredState. (set-vars init vv-pairs)
                            context
                            {:puts (into (:puts (meta state)) vv-pairs)}
                            {}))
   (list-vars [] (list-vars init))
   (as-map [] init)
  LoggingState
   (extract-effects []  (util/safe-get (meta state) :puts))
   (ooc-effects     []  (util/filter-map #(not (.contains context (key %))) (util/safe-get (meta state) :puts)))
  ContextualState 
   (current-context []  context)
   (extract-context [c] (fast-select-keys init c))
   (apply-effects   [e] (set-vars state e))
   (get-logger      [c] (make-logging-factored-state (as-map init) c)))

(defn make-logging-factored-state [init-state context] 
  (LoggingFactoredState init-state context {:puts {}} {}))

(defn enforce-logger [state]
  (assert (= (type state) ::LoggingFactoredState))
  state)


(def *m1* {:set-var assoc :set-vars into :get-var util/safe-get :list-vars keys :as-map identity})
(def *m2* {:current-context util/keyset :extract-context select-keys 
                   :apply-effects into :get-logger make-logging-factored-state})

(extend clojure.lang.PersistentHashMap FactoredState *m1*  ContextualState *m2*)
(extend clojure.lang.PersistentArrayMap FactoredState *m1*  ContextualState *m2*)

;(def *m3* {:set-var assoc! :get-var util/safe-get :list-vars keys :as-map persistent!})
;(extend clojure.lang.PersistentHashMap$TransientHashMap
;  FactoredState *m3* ContextualState *m2*)
;(extend clojure.lang.PersistentArrayMap$TransientArrayMap
;  FactoredState *m3* ContextualState *m2*)

(defn state-matches-map? [fs m]
  (every? (fn [[k v]] (= (get-var fs k) v)) m))

(deftest test-logging-factored-state
  (let [si {:a 1 :b 2 :c 3}
        s1 (get-logger si #{:a})
        s2 (set-var s1 :a 1)
        s3 (set-var s1 :b 2)
        s4 (set-var (set-var s1 :a 1) :b 2)
        s5 (set-var (set-var s1 :a 1) :c 4)
        ss [s1 s2 s3 s4 s5]
        equal-sets [#{0 1} #{2 3} #{4}]
        ]
    (is (= (map as-map          ss) [si si si si (assoc si :c 4)]))
    (is (= (map extract-effects ss) [{} {:a 1} {:b 2} {:a 1 :b 2} {:a 1 :c 4}]))
    (is (= (map ooc-effects     ss) [{} {} {:b 2} {:b 2} {:c 4}]))
    (doseq [es equal-sets] 
      (is (apply = (map ss es)))
      (is (apply = (map (comp hash ss) es))))
    (doseq [[s1 s2] (util/combinations equal-sets 2), i1 s1, i2 s2]
      (is (not (= i1 i2)))
      (is (not (= (hash i1) (hash i2)))))))

;; TODO: make method so we can use transients?



;(defn get-logging-state-gets [s] @(:gets (meta s)))
;(defn get-logging-state-puts [s] (util/safe-get (meta s) :puts))




(defprotocol Action
  (primitive? [a])
  (action-name [a]))

(defprotocol PrimitiveAction
  (applicable? [a s])
  (next-state-and-reward  [a s]) ; Precondition: applicable.
  )

(defprotocol ContextualAction
  (precondition-context [a s]))

;; TODO: better to have single map from state to range ?
(defprotocol AngelicAction
  (optimistic-map [a s])
  (pessimistic-map [a s]))

(deftype FactoredPrimitive [name precond-map effect-map reward] :as this
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
      (.keySet #^Map precond-map))
  AngelicAction
    (optimistic-map [s]
      (if (applicable? this s) 
        (let [[s r] (next-state-and-reward this s)] {s r}) 
        {}))
    (pessimistic-map [s]
      (if (applicable? this s) 
        (let [[s r] (next-state-and-reward this s)] {s r}) 
        {})))

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
;  (println "Progressing" action state)
  (util/sref-set! *next-counter* (inc (util/sref-get *next-counter*)))
 ; (.put #^HashMap *next-ba* (action-name action) (inc (get *next-ba* (action-name action) 0)))
  (let [[next reward] (next-state-and-reward action state)
        old-meta      (meta state)]
    [(vary-meta next assoc
       :act-seq (cons (action-name action) (:act-seq old-meta))
                                        ;(conj (or (:act-seq (meta state)) []) action)
       :reward (+ reward (or (:reward old-meta) 0)))
     reward]))

(defn successor-seq [actions state]
  (loop [actions actions state state rew 0]
    (if (not actions) [state rew]
      (let [[f & r] actions]
        (util/assert-is  (applicable? f state))
        (let [[next-state step-rew] (next-state-and-reward f state)]
          (recur r next-state (+ rew step-rew)))))))

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

(defn make-finish-action [env]
  (FactoredPrimitive 
    '[finish]
    (goal-map env)
    (zipmap (list-vars (initial-state env)) (repeat :goal))
    0))

(defn make-finish-goal-state [env]
  (zipmap (list-vars (initial-state env)) (repeat :goal)))

(defn verify-solution [env [sol rew]]
  (let [[result result-rew] (successor-seq sol (initial-state env))]
    (util/assert-is ((goal-fn env) result))
    (assert (= result-rew rew))
    [sol rew]))


