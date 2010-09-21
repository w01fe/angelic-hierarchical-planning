(ns angelic.search.incremental.implicit-ah-astar
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is])
  (:import  [java.util HashMap]))


;; Simple implicit version of AHA* with implicit descritpions.
;; TODO: improved caching, et.c  This is jsut quick and dirty.
;; TODO: add pruning.

;(def ^HashMap *heuristic-cache* nil)

; tuples are [init-set init-rew init-solved?]

(defrecord ActionNode [input-tuple constraint action])

(defn make-action-node [input-tuple constraint action]
  (ActionNode. input-tuple constraint action))

(defn action-node-name [an] [(:constraint an) (env/action-name (:action an))])

(defn action-node-output [an]
  (let [{:keys [input-tuple constraint action]} an
        [ss rew solved?] input-tuple
        [opt-ss step-rew] (angelic/optimistic-set-and-reward action (state-set/constrain ss constraint))]
    (when (and opt-ss (not (state-set/empty? opt-ss)) (not (= is/neg-inf step-rew)))
      [opt-ss (+ rew step-rew) (and solved? (env/primitive? action))])))

(defn make-action-node-seq
  "Make a seq, or nil for failure."
  [input-tuple constraint-action-pairs]
  (if (empty? constraint-action-pairs)
    ()    
    (let [[[c f] & r] constraint-action-pairs
          nxt (make-action-node input-tuple c f)]
      (when-let [tup (action-node-output nxt)]
        (when-let [rst (make-action-node-seq tup r)]
          (cons nxt rst))))))


(defn action-node-refinable? [an]
  (let [{:keys [input-tuple constraint action]} an
        ss (first input-tuple)]
;    (println (env/action-name action))
    (and (not (env/primitive? action))
         (angelic/can-refine-from-set? action ss))))

(defn action-node-refinements [an suffix-nodes]
  (assert (action-node-refinable? an))
  (let [{:keys [input-tuple constraint action]} an
        [ss rew solved?] input-tuple]
    (remove #{nil}
      (for [[new-constraint ref] (angelic/immediate-refinements-set action ss)
            :let [first-constraint     (merge-with clojure.set/intersection constraint new-constraint)]]
        (make-action-node-seq
         input-tuple
         (concat
          (if (empty? ref)
            [[first-constraint env-util/+factored-noop+]]
            (cons [first-constraint (first ref)] (map #(vector {} %) (rest ref))))
          (map (juxt :constraint :action) suffix-nodes)))))))


(defrecord Plan [node-seq output-tuple])

(defn make-plan [node-seq]
  (assert (seq node-seq))
  (Plan. node-seq (action-node-output (last node-seq))))

(defn plan-name [plan]
  (map action-node-name (:node-seq plan)))

(defn plan-refinements [plan]
  (let [nodes (:node-seq plan)
        [prefix-plus suffix] (split-with #(nth (:input-tuple %) 2) nodes)
        prefix (butlast prefix-plus)
        ref    (last prefix-plus)]
;    (println (map action-node-name nodes))
;    (println (map :input-tuple nodes))
;    (println (count prefix-plus) (count suffix))
    (for [ref-seq (action-node-refinements ref suffix)] 
      (make-plan (concat prefix ref-seq))))
  )


(defrecord ImplicitAHA*FEnv [henv]
  env/Env
  (initial-state [_]
    (let [e    (hierarchy/env henv)
          init (env-util/initial-logging-state e)
          tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)] 0)]
      (-> (make-action-node [(state-set/make-logging-factored-state-set [init]) 0 true] {} tla)
                       vector
                       make-plan)))
  (actions-fn [_]
    (fn [shp]
      (for [ref (plan-refinements shp)]
        (reify 
         env/Action
         (action-name [_] (plan-name ref))
         env/PrimitiveAction
         (applicable? [_ s] (assert (identical? s shp)) true)
         (next-state-and-reward [_ s]
           (let [old-rew (second (:output-tuple shp))
                 new-rew (second (:output-tuple ref))]
                                        ;             (println old-rew shp new-rew)
             (util/assert-is (<= new-rew old-rew) "%s" (print-str shp ref))
             [ref (- new-rew old-rew)]))))))
  (goal-fn [_] (fn [s] (nth (util/safe-get s :output-tuple) 2))))

(defn make-implicit-first-ah-a*-env [henv] (ImplicitAHA*FEnv. henv))

(defn plan->implicit-aha-star-node [plan]
  (let [{:keys [node-seq output-tuple]} plan
        [_ rew solved?] output-tuple]
    (is/make-simple-node (plan-name plan) rew solved? plan)))

(defn make-aha-star-simple-search [root-plan]
  (is/make-flat-incremental-dijkstra 
   (plan->implicit-aha-star-node root-plan)
   #(->> % :data plan-refinements (map plan->implicit-aha-star-node))))

(defn implicit-first-ah-a* [henv]
  (let [e    (hierarchy/env henv)
        init (env-util/initial-logging-state e)
        tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
;    (binding [*heuristic-cache*    (HashMap.)])
    (when-let [g (-> (make-action-node [(state-set/make-logging-factored-state-set [init]) 0 true] {} tla)
                     vector
                     make-plan
                     make-aha-star-simple-search
                     is/first-goal-node
                     :data)]
      [(remove #{[:noop]} (map #(env/action-name (:action %)) (:node-seq g)))
       (second (:output-tuple g))])))



;; TODO: ImplicitAHA*Env
