(ns exp.hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env]
            ))



(def *ref-counter* (util/sref 0))
(def *plan-counter* (util/sref 0))

(defn reset-ref-counter [] 
  (util/sref-set! *ref-counter* 0)
  (util/sref-set! *plan-counter* 0)  
  )

(defprotocol HighLevelAction
  (immediate-refinements- [a s])
  (cycle-level- [a s]))

;; TODO: this forces eagerness, may not be desirable in some situations.
(defn immediate-refinements [a s]  
  ;(println "Refs for " (env/action-name a) "from" (map #(env/get-var s %) '[[atx] [aty]]))
;  (println "Computing Refs for " (env/action-name a))
  (util/timeout)
  (let [refs (immediate-refinements- a s)]
  #_  (println "\nRefs for " (env/action-name a) ;"from" (env/as-map s) "are" 
             (apply str (doall (map #(str "\n  " (util/str-join ", " (map env/action-name %))) refs))))
    (util/sref-set! *ref-counter*  (+ 1            (util/sref-get *ref-counter*)))
    (util/sref-set! *plan-counter* (+ (count refs) (util/sref-get *plan-counter*)))
    refs))

(defn cycle-level [a s]
  (when-not (env/primitive? a)
    (cycle-level- a s)))

(deftype TopLevelAction [env initial-plans]
  env/Action           (action-name [] ['act])
                       (primitive? [] false)  
  env/ContextualAction (precondition-context [s] (env/current-context (env/initial-state env)))
  HighLevelAction      (immediate-refinements- [s] initial-plans)
                       (cycle-level- [s] nil)
  env/AngelicAction    (optimistic-map [s]
                         {(env/set-vars s (env/make-finish-goal-state env)) 
                          Double/POSITIVE_INFINITY})
                       (pessimistic-map [s] {}))




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
  (let [[prim-prefix high-level-suffix] (split-with #(env/primitive? %) rest-plan)
        prim-result (successor-seq prim-prefix state)]
    (when prim-result   
      (ShopHTNPlan high-level-suffix prim-result))))


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




 ;;; These types remove state abstraction from a hierarchy.

(declare wrap-action-nsa)

(deftype NSAPrimitive [a full-context]
  env/Action                (action-name [] (env/action-name a))
                            (primitive? [] true)  
  env/ContextualAction      (precondition-context [s] full-context)
  env/PrimitiveAction       (applicable? [s] (env/applicable? a s)) 
                            (next-state-and-reward [s] (env/next-state-and-reward a s)))

(deftype NSAHLA       [a full-context]
  env/Action                (action-name [] (env/action-name a))
                            (primitive? [] false)  
  env/ContextualAction      (precondition-context [s] full-context)
  HighLevelAction (immediate-refinements- [s]
                             (map (fn [ref] (map #(wrap-action-nsa % full-context) ref))
                              (immediate-refinements- a s)))
                            (cycle-level- [s] (cycle-level- a s)))

(defmethod print-method ::NSAPrimitive [a o] (print-method (env/action-name a) o))
(defmethod print-method ::NSAHLA [a o] (print-method (env/action-name a) o))

(defn wrap-action-nsa [a full-context]
  (if (env/primitive? a) 
    (NSAPrimitive a full-context)
    (NSAHLA a full-context)))

;; Can take more progressions than flat because 