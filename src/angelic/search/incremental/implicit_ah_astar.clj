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

(def ^HashMap *heuristic-cache* nil)

; tuples are [init-set init-rew init-solved?]

(defrecord ActionNode [init-tuple constraint action])

(defn make-action-node [init-tuple constraint action]
  (ActionNode. init-tuple constraint action))

(defn action-node-name [an] [(:constraint an) (env/action-name (:action an))])

(defn action-node-output [an]
  (let [{:keys [init-tuple constraint action]} an
        [ss rew solved?] init-tuple
        [opt-ss step-rew] (angelic/optimistic-set-and-reward action (state-set/constrain ss constraint))]
    (when (and opt-ss (not (state-set/empty? opt-ss)) (not (= is/neg-inf step-rew)))
      [opt-ss (+ rew step-rew) (and solved? (env/primitive? action))])))

(defn make-action-node-seq
  "Make a seq, or nil for failure."
  [init-tuple constraint-action-pairs]
  (if (empty? constraint-action-pairs)
    ()    
    (let [[[c f] & r] constraint-action-pairs
          nxt (make-action-node init-tuple c f)]
      (when-let [tup (action-node-output nxt)]
        (when-let [rst (make-action-node-seq tup r)]
          (cons nxt rst))))))


(defn action-node-refinable? [an]
  (let [{:keys [init-tuple constraint action]} an
        ss (first init-tuple)]
    (and (not (env/primitive? action))
         (angelic/can-refine-from-set? action ss))))

(defn action-node-refinements [an suffix-nodes]
  (assert (action-node-refinable? an))
  (let [{:keys [init-tuple constraint action]} an
        [ss rew solved?] init-tuple]
    (remove nil
      (for [[new-constraint ref] (angelic/immediate-refinements-set action ss)
            first-constraint     (merge-with clojure.set/intersection constraint new-constraint)]
        (make-action-node-seq
         init-tuple
         (concat
          (if (empty? ref)
            [[first-constraint env-util/+factored-noop+]]
            (cons [first-constraint (first ref)] (map #(vector {} %) (rest ref))))
          (map (juxt :constraint :action) suffix-nodes)))))))


(defrecord Plan [node-seq output-tuple])

(defn make-plan [node-seq]
  (assert (seq node-seq))
  (Plan. node-seq (action-node-output (last node-seq))))

(defn plan->implicit-aha-star-node [plan]
  (let [{:keys [node-seq output-tuple]} plan
        [_ rew solved?] output-tuple]
    (is/make-simple-node (map action-node-name node-seq) rew solved? plan)))

(defn plan-refinements [plan]
  (let [nodes (:node-seq plan)
        [prefix more-nodes] (split-with #(nth (:input-tuple %) 2) nodes)
        [ref & suffix] more-nodes]
    (for [ref-seq (action-node-refinements ref suffix)]
      (make-plan (concat prefix ref-seq)))))


(defn make-aha-star-simple-search [root-plan]
  (is/make-flat-incremental-dijkstra 
   (plan->implicit-aha-star-node root-plan)
   (fn [node]
     (let [plan (:data node)]))
   #(->> % :data plan-refinements (map plan->implicit-aha-star-node))))

(defn implicit-first-ah-a* [henv]
  (let [e    (hierarchy/env henv)
        init (env-util/initial-logging-state e)
        tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
    (binding [*heuristic-cache*    (HashMap.)]
      (when-let [g (-> (make-plan-node [(state-set/make-logging-factored-state-set [init]) 0 true] {} tla)
                       vector
                       make-plan
                       make-aha-star-simple-search
                       is/first-goal-node
                       :data)]
        [(map #(env/action-name (:action %)) (:node-seq g))
         (second (:output-tuple g))]))))


;; TODO: ImplicitAHA*Env
