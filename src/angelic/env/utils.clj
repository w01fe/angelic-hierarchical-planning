(ns w01fe.env.utils
  (:require [edu.berkeley.ai.util :as util])
  (:import [java.util Set Map])
  )

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
    (optimistic-map- [s]
      (if (applicable? this s) 
        (let [[s r] (next-state-and-reward this s)] {s r}) 
        {}))
    (pessimistic-map- [s]
      (if (applicable? this s) 
        (let [[s r] (next-state-and-reward this s)] {s r}) 
        {})))

(defmethod print-method ::FactoredPrimitive [a o] (print-method (action-name a) o))

(defn compose-factored-primitives [fp1 fp2]
  (let [e1 (:effect-map fp1), p2 (:precond-map fp2)
        common-keys (clojure.set/intersection (util/keyset e1) (util/keyset p2))]   
    (assert (= (select-keys e1 common-keys) (select-keys p2 common-keys)))
    (FactoredPrimitive 
     [::Composed (:name fp1) (:name fp2)]
     (util/merge-agree (:precond-map fp1) (apply dissoc p2 common-keys))
     (merge e1 (:effect-map fp2))
     (+ (:reward fp1) (:reward fp2)))))

 


(defn successor-seq [actions state]
  (loop [actions actions state state rew 0]
    (if (not actions) [state rew]
      (let [[f & r] actions]
        (util/assert-is  (applicable? f state))
        (let [[next-state step-rew] (next-state-and-reward f state)]
          (recur r next-state (+ rew step-rew)))))))

(defn concat-solution-pairs [& pairs]
  [(apply concat (map first pairs)) (apply + 0 (map second pairs))])




(deftype SimpleFactoredEnv [init a-fn g-map]
  Env 
   (initial-state [] init)
   (actions-fn    [] a-fn)
   (goal-fn       [] #(when (state-matches-map? % g-map) (solution-and-reward %)))
  FactoredEnv
   (goal-map [] g-map))



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


