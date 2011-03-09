(ns angelic.env.util
  (:require [angelic.util :as util]
	        [angelic.env :as env]
	        [angelic.env.state :as state]))

(defrecord FactoredPrimitive [name precond-map effect-map reward] 
  env/Action 
    (action-name [this] name)
    (primitive?  [this] true)
  env/PrimitiveAction 
    (applicable? [this s]
      (every? (fn [[var val]] (= (state/get-var s var) val)) precond-map))
    (next-state-and-reward [this s]
      [(state/apply-effects s effect-map) reward])
  env/ContextualAction
    (precondition-context [this s]
      (.keySet #^java.util.Map precond-map)))

(defn make-factored-primitive [name precond-map effect-map reward]
  (FactoredPrimitive. name precond-map effect-map reward))

(def +factored-noop+ (FactoredPrimitive. [:noop] {} {} 0))

(defmethod print-method FactoredPrimitive [a o] (print-method (env/action-name a) o))



(defn successor-seq [actions state]
  (loop [actions actions state state rew 0]
    (if (not actions) [state rew]
      (let [[f & r] actions]
        (util/assert-is  (env/applicable? f state))
        (let [[next-state step-rew] (env/next-state-and-reward f state)]
          (recur r next-state (+ rew step-rew)))))))

(defn concat-solution-pairs [& pairs]
  [(apply concat (map first pairs)) (apply + 0 (map second pairs))])




(defrecord SimpleFactoredEnv [init a-fn g-map]
  env/Env 
   (initial-state [this] init)
   (actions-fn    [this] a-fn)
   (goal-fn       [this] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
   (goal-map      [this] g-map))

(defn make-simple-factored-env [init a-fn g-map]
  (SimpleFactoredEnv. init a-fn g-map))


(defn initial-logging-state [env]
  (let [init (env/initial-state env)]
    (state/get-logger init (state/current-context init))))

(defn make-finish-action [env]
  (FactoredPrimitive.
    '[finish]
    (env/goal-map env)
    (zipmap (state/list-vars (env/initial-state env)) (repeat :goal))
    0))

(defn make-finish-goal-state [env]
  (zipmap (state/list-vars (env/initial-state env)) (repeat :goal)))

(defn verify-solution [env [sol rew]]
  (let [[result result-rew] (successor-seq sol (env/initial-state env))]
    (util/assert-is ((env/goal-fn env) result))
    (assert (= result-rew rew))
    [sol rew]))




(comment ; not in use...
(defn compose-factored-primitives [fp1 fp2]
  (let [e1 (:effect-map fp1), p2 (:precond-map fp2)
        common-keys (clojure.set/intersection (util/keyset e1) (util/keyset p2))]   
    (assert (= (select-keys e1 common-keys) (select-keys p2 common-keys)))
    (env-util/make-factored-primitive 
     [::Composed (:name fp1) (:name fp2)]
     (util/merge-agree (:precond-map fp1) (apply dissoc p2 common-keys))
     (merge e1 (:effect-map fp2))
     (+ (:reward fp1) (:reward fp2))))))


