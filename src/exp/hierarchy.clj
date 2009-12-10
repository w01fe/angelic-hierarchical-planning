(ns exp.hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env]
            ))


(defprotocol HighLevelAction
  (immediate-refinements [a s])
  (cycle-level- [a s]))

(deftype TopLevelAction [env initial-plans]
  env/Action           (action-name [] ['act])
  env/ContextualAction (precondition-context [] (keys (env/initial-state env)))
  HighLevelAction      (immediate-refinements [s] initial-plans)
                       (cycle-level- [s] nil))

(defn cycle-level [a s]
  (and (satisfies? HighLevelAction a)
       (cycle-level- a s)))

;(deftype SimpleFactoredHLA [name relevant-vars ref-fn] 
;  env/Action           (action-name [] name)
;  env/ContextualAction (precondition-context [] relevant-vars)
;  HighLevelAction      (immediate-refinements [s] (ref-fn s)))


(defprotocol HierarchicalEnv (env [h]) (initial-plan [h]))

(deftype SimpleHierarchicalEnv [env initial-plan] 
 HierarchicalEnv
  (env          [] env)
  (initial-plan [] initial-plan))

(deftype ShopHTNPlan [rest-plan state])

(defmethod print-method ::ShopHTNPlan [p os] 
  (let [[sol rew] (env/solution-and-reward (:state p))]
    (print-method  [(map env/action-name sol) rew (map env/action-name (:rest-plan p))]
                   os)))

(defn successor-seq [actions state]
  (if (empty? actions) state
    (let [[first-action & rest-actions] actions]
      (when (= (env/action-name first-action) '[finish]) (print "."))
      (when (env/applicable? first-action state)
        (recur rest-actions (first (env/successor first-action state)))))))

(defn normalized-plan [rest-plan state]
  (let [[prim-prefix high-level-suffix] (split-with #(satisfies? env/PrimitiveAction %) rest-plan)
        prim-result (successor-seq prim-prefix state)]
    (when prim-result   
      (ShopHTNPlan high-level-suffix prim-result))))

(def *ref-counter* (util/sref 0))
(def *plan-counter* (util/sref 0))

(defn reset-ref-counter [] 
  (util/sref-set! *ref-counter* 0)
  (util/sref-set! *plan-counter* 0)  
  )

(deftype ShopHTNEnv [he] env/Env
  (initial-state [] (util/make-safe (normalized-plan (initial-plan he) (env/initial-state (env he)))))
  (actions-fn []
    (fn [shp]
;      (println shp)
      (let [[first-action & rest-plan] (:rest-plan shp)
            state                    (:state shp)]
        (util/sref-set! *ref-counter* (inc (util/sref-get *ref-counter*)))
        (for [[i ref] (util/indexed (immediate-refinements first-action state))
              :let [result (normalized-plan (concat ref rest-plan) state)]
              :when result]
          (reify 
           env/Action
            (action-name [] 
              [ref (env/action-name first-action) i])
           env/PrimitiveAction
            (applicable? [s] 
              (assert (identical? s shp)) 
              true)
            (next-state-and-reward [s] 
              ;(println result)
              (assert (identical? s shp))
              (util/sref-set! env/*next-counter* (dec (util/sref-get env/*next-counter*))) ;; uncount this.
              (util/sref-set! *plan-counter* (inc (util/sref-get *plan-counter*))) ;; uncount this.
              [result (- (env/reward (:state result)) (env/reward state))]))))))
  (goal-fn [] (fn [s] 
                    (when (empty? (:rest-plan s))
                      (env/solution-and-reward (:state s))))))

(defn run-counted [f]
  (env/reset-next-counter)
  (reset-ref-counter)
  [(f) (util/sref-get env/*next-counter*) (util/sref-get *ref-counter*) (util/sref-get *plan-counter*)])


;; Can take more progressions than flat because 