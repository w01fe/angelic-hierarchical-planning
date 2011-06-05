(ns angelic.hierarchy.util
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]
            [angelic.env.util :as envutil]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.angelic :as angelic]
            ))

;; Collection of various unrelated utils for making hierarchies.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generic HLA types ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrecord TopLevelAction [env initial-plans reward]
  env/Action
  (action-name [_] ['act (hash initial-plans)])
  (primitive?  [_] false)  

  env/ContextualAction
  (precondition-context [_ s] (state/current-context (env/initial-state env)))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s] initial-plans)
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    {(state/set-vars s (envutil/make-finish-goal-state env)) 
     reward})
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] (state/current-context (env/initial-state env)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss] (for [p initial-plans] [{} p]))
  (optimistic-set-and-reward- [a ss]
    [(state/set-vars ss (util/map-vals (fn [x] #{x}) (envutil/make-finish-goal-state env)))
     reward])
  (pessimistic-set-and-reward- [a ss] nil))


(defn make-top-level-action
  ([env initial-plans] (make-top-level-action env initial-plans Double/POSITIVE_INFINITY))
  ([env initial-plans reward]
     (TopLevelAction. env initial-plans reward)))

(defrecord SimpleHLA [name pc refs]
  env/Action
  (action-name [_] name)
  (primitive?  [_] false)  

  env/ContextualAction
  (precondition-context [_ s] pc)

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s] refs)
  (cycle-level-           [_ s] nil))

(defn make-simple-hla [name pc refs]
  (SimpleHLA. name pc refs))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Generic HEnv ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrecord SimpleHierarchicalEnv [env initial-plan] 
  hierarchy/HierarchicalEnv
  (env          [_] env)
  (initial-plan [_] initial-plan))

(defn make-simple-hierarchical-env [env initial-plan]
  (SimpleHierarchicalEnv. env initial-plan))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; ShopHTNENV ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turns a hierarchical env into a regular env using SHOP trick.

(defrecord ShopHTNPlan [rest-plan state])

(defmethod print-method ShopHTNPlan [p os] 
  (let [[sol rew] (env/solution-and-reward (:state p))]
    (print-method  [(map env/action-name sol) rew (map env/action-name (:rest-plan p))]
                   os)))

(defn- successor-seq [actions state]
  (if (empty? actions) state
    (let [[first-action & rest-actions] actions]
      (when (= (env/action-name first-action) '[finish]) (print "."))
      (when (env/applicable? first-action state)
        (recur rest-actions (first (env/successor first-action state)))))))

(defn- normalized-plan [rest-plan state]
  (let [[prim-prefix high-level-suffix] (split-with #(env/primitive? %) rest-plan)
        prim-result (successor-seq prim-prefix state)]
    (when prim-result   
      (ShopHTNPlan. high-level-suffix prim-result))))

(defrecord ShopHTNEnv [he]
  env/Env
  (initial-state [_] (util/make-safe (normalized-plan (hierarchy/initial-plan he) (env/initial-state (hierarchy/env he)))))
  (actions-fn [_]
    (fn [shp]
      (let [[first-action & rest-plan] (:rest-plan shp)
            state                    (:state shp)]
        (util/sref-set! hierarchy/*ref-counter* (inc (util/sref-get hierarchy/*ref-counter*)))
        (for [[i ref] (util/indexed (hierarchy/immediate-refinements first-action state))
              :let [result (normalized-plan (concat ref rest-plan) state)]
              :when result]
          (reify 
           env/Action
            (action-name [_] 
              [ref (env/action-name first-action) i])
           env/PrimitiveAction
            (applicable? [_ s] 
              (assert (identical? s shp)) 
              true)
            (next-state-and-reward [_ s] 
              (assert (identical? s shp))
              (util/sref-set! env/*next-counter* (dec (util/sref-get env/*next-counter*))) ;; uncount this.
              (util/sref-set! hierarchy/*plan-counter* (inc (util/sref-get hierarchy/*plan-counter*))) ;; uncount this.
              [result (- (env/reward (:state result)) (env/reward state))]))))))
  (goal-fn [_]
    (fn [s] 
      (when (empty? (:rest-plan s))
        (env/solution-and-reward (:state s))))))

(defn make-shop-htn-env [he] (ShopHTNEnv. he))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;; Anti-State-Abstraction Wrappers ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ;;; These types remove state abstraction from a hierarchy.

(declare wrap-action-nsa)

(defrecord NSAPrimitive [a full-context]
  env/Action
  (action-name [_] (env/action-name a))
  (primitive?  [_] true)  

  env/ContextualAction
  (precondition-context [_ s] full-context)

  env/PrimitiveAction
  (applicable?           [_ s] (env/applicable? a s)) 
  (next-state-and-reward [_ s] (env/next-state-and-reward a s)))

(defrecord NSAHLA       [a full-context]
  env/Action
  (action-name [_] (env/action-name a))
  (primitive?  [_] false)  

  env/ContextualAction
  (precondition-context [_ s] full-context)

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (map (fn [ref] (map #(wrap-action-nsa % full-context) ref))
         (hierarchy/immediate-refinements- a s)))
  (cycle-level-           [_ s] (hierarchy/cycle-level- a s)))

(defmethod print-method ::NSAPrimitive [a o] (print-method (env/action-name a) o))
(defmethod print-method ::NSAHLA [a o] (print-method (env/action-name a) o))

(defn wrap-action-nsa [a full-context]
  (if (env/primitive? a) 
    (NSAPrimitive. a full-context)
    (NSAHLA. a full-context)))
