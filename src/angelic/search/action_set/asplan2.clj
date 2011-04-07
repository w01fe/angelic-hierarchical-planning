(ns angelic.search.action-set.asplan2
  (:require [angelic.util :as util]
            [angelic.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis])
  (:import [java.util HashMap]))


;; New version.
;; Instead of choosing actions, together choose:
;;   set of child intentions (all succeed or single failure), next value for each child variable.
;; (next value can be left abstract, ignore this possibility for now.
;; This can't work.

;; Instead, we can do:
;;  choose an action set, narrow it.
;;  note: being blocked does not change the set.
;;  set is applicable iff there exists an action in the set with a precondition
;;  that is neither blocked nor reserved.
;;  actions with no preconditions are always immediately fired, don't live in the set.

;; First incarnation just for unary domains

;; TODOS:
;; - multiple effects
;; - Possible next children (i.e., blocks held)
;; - Auxiliary variables
;; - Top-down mode?
;; ...
;; - Hueristic costs.
;; Focusing on fail-fast case (repairing blocks).

;; Investigate simply not-x choice.
;; Means even bigger state space, hopefully not that big since we get to choose how to explore.


;; Note: not actually possible always to reserve all preconds at once.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

(defn target-var [v] [:target v]) ; a value for v, :wait if no target.
(defn possible-children-var [v]  [:children v]) ; a set of child vars
(defn possible-actions-var [v]  [:actions v]) ; a set of actions, :wait if no target.

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a child (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init child-var-map goal-action]
  (let [vars (keys child-var-map)]
    (into {}
      (concat 
       (for [v vars] [v (state/get-var init v)])
       (for [v vars] [(target-var v) :wait])
       (for [v vars] [(possible-children-var v) (child-var-map v)])
       (for [v vars] [(possible-actions-var v) :wait])
       [[(target-var sas/goal-var-name) sas/goal-true-val]]
       [[(possible-actions-var sas/goal-var-name) #{goal-action}]]))))

(defn action-effect-var [a] (util/safe-singleton (keys (:effect-map a))))




(defn make-assign-actions-action [v actions]
  (assert (set? actions))
  (env-util/make-factored-primitive
   [::AssignActions v actions]
   {}
   {(possible-actions-var v) actions}
   0))

(defn make-assign-children-action [p children]
  (assert (set? children))
  (env-util/make-factored-primitive
   [::AssignChildren p children]
   {}
   {(possible-children-var p) children}
   0))

(defn make-commitment-action [p c cur-val dst-val wanting-actions possible-actions-fn]
  (assert (not (= cur-val dst-val)))
  (assert (set? wanting-actions))
  (env-util/make-factored-primitive
   [::Commit p c dst-val wanting-actions]
   {}
   {(possible-children-var p) #{c}
    (possible-actions-var c) wanting-actions
    (target-var p) dst-val
    (possible-actions-var p) (possible-actions-fn p cur-val dst-val)}
   0))

(defn make-greedy-fire-action [s a effect-var cvm possible-actions-fn]
  (doseq [[pvar pval] (dissoc (:precond-map a) effect-var)]
    (assert (= (state/get-var s pvar) pval))
    (assert (= (state/get-var s (possible-actions-var pvar)) :wait)))  
  (env-util/make-factored-primitive
   [::Fire a]
   {}
   (into (:effect-map a)
         (cons
          [(possible-actions-var effect-var)
           (let [cur-val (get (:effect-map a) effect-var)
                 dst-val (state/get-var s (target-var effect-var))]
             (assert (not (= dst-val :wait)))
             (if (= cur-val dst-val) :wait (possible-actions-fn effect-var cur-val dst-val)))]           
          (apply concat
                 (for [[pvar pval] (dissoc (:precond-map a) effect-var)]
                   [[(possible-children-var pvar) (cvm pvar)]
                    [(possible-actions-var pvar) :wait]
                    [(target-var pvar) :wait]]))))
   (:reward a)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitive Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn backward-reachable-nodes-and-preds [^HashMap cache simple-dtgs var-name to-val]
  (util/cache-with cache [:backward var-name to-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (map reverse (util/safe-get simple-dtgs var-name)) to-val)))

(defn possibly-acyclic-successors
  "Return a list of successors of cur-val, which can potentially lead to dst-val
   without a cycle."  
  [cache simple-dtgs var cur-val dst-val]
  (let [backward-sets (backward-reachable-nodes-and-preds cache simple-dtgs var dst-val)]
    (for [[s t] (util/safe-get simple-dtgs var)
          :when (and (= s cur-val) (not (contains? (backward-sets t) s)))]
      t)))

(defn make-possible-actions-fn [dtgs]
  (let [simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (fn [var cur-val dst-val]
      (for [nxt-val (acyclic-succ-fn var cur-val dst-val),
            a       (get-in dtgs [var cur-val nxt-val])]
        a))))




(defn greedy-action? [s a effect-var]
  (assert (= effect-var (action-effect-var a)))
  (and (state/state-matches-map? s (:precond-map a))
       (every? #(contains? (state/get-var s (possible-children-var %)) effect-var)
               (keys (dissoc (:precond-map a) effect-var)))))





;; return a list of actions, or nil if no greedy possibilities.
(defn greedy-actions [s v cvm possible-actions-fn]
  (let [actions (state/get-var s (possible-actions-var v))
        [greedy not-greedy]    (when-not (= :wait actions) (util/separate #(greedy-action? s % v) actions))]
    (when (seq greedy)
      (concat
       (when (seq not-greedy) [(make-assign-actions-action v (set not-greedy))])
       (for [a greedy] (make-greedy-fire-action s a v cvm possible-actions-fn))))))

;; TODO: treat happy same as concerned?
;; Split based on:
;;  split out actions that don't care about p or want current value of p.
;;  no reservation of p (if remaining vals)
;;  reserve p, split on target-val for p.
(defn refinement-actions [s p c possible-actions-fn]
  (let [actions (state/get-var s (possible-actions-var c))
        children (state/get-var s (possible-children-var p))
        cur-val  (state/get-var s p)
        [concerned indifferent] (util/separate #(contains? (:precond-map %) p) actions)
        [happy unhappy]         (util/separate #(= (get (:precond-map %) p) cur-val) concerned)
        lazy-set                (set (concat happy indifferent))]
    (assert (not-any? #(greedy-action? s % c) actions))
    (assert (seq unhappy))
    (assert (contains? children c))
    (assert (= :wait (state/get-var s (target-var p))))
    (concat
     (when-not (empty? lazy-set)
       [(make-assign-actions-action c lazy-set)])
     (when (> (count children) 1)
       [(make-assign-children-action p (disj children c))])
     (for [[dst-val wanting-actions] (group-by #((:precond-map %) p) unhappy)]
       (make-commitment-action p c cur-val dst-val (set wanting-actions) possible-actions-fn)))))

(defn var-precondition-choices [s v]
  (let [actions (state/get-var s (possible-actions-var v))]
    (when-not (= actions :wait)
      (filter
       (fn [p] (and (= :wait (state/get-var s (target-var p)))
                    (contains? (state/get-var s (possible-children-var p)) v)
                    (some #(when-let [v (get (:precond-map %) p)] (not (= (state/get-var s p) v))) actions)))       
       (distinct (apply concat (map (comp keys :precond-map) actions)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ASPlanEnv [base-sas-env init actions-fn g-map]
  env/Env 
    (initial-state [e] init)
    (actions-fn    [e] actions-fn)
    (goal-fn       [e] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [e] g-map))


(defn make-asplan-env
  "Make an actino-set planning environment.  Switches are:
    check-deadlock?: check for cycles in precedence graph above and beyond lack of sources
    check-components?: check for disconnected components, rule out sources outside of goal comp
    edge-rule: :naive, :greedy, :sloppy, or :extra-sloppy.
       Naive means we stick exactly to the simple semantics of the vanilla actions.
       Greedy means we forget about reserving preconditions when free and we can fire right now (less branching).
       Sloppy means we ignore if preconditions are free, but require no action on them.
       Extra-sloppy means anything goes -- if you can execute ignoring commitments, go for it."
  ([sas-problem]
     (let [causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
           vars          (graphs/ancestor-set causal-graph [sas/goal-var-name])
           causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
           tsi           (graphs/df-topological-sort-indices causal-graph) ;; TODO: doesn't seem to matter...
           child-var-map (assoc (util/map-vals #(set (map second %)) (group-by first causal-graph))
                           sas/goal-var-name #{})
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           possible-actions-fn (make-possible-actions-fn dtgs)]
;       (assert (graphs/dag? causal-graph))    
       (assert (sas-analysis/unary? sas-problem))
;       (println child-var-map)
       
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))

        (fn asplan-actions [s]
;          (println "\n"(:act-seq (meta s)))
          (identity #_ util/prln (or (some #(greedy-actions s % child-var-map possible-actions-fn) vars)
               (let [choices (for [v vars, p (var-precondition-choices s v)]
                               (refinement-actions s p v possible-actions-fn))]
;                 (when (empty? choices) (clojure.inspector/inspect-tree (state/as-map s)) #_ (assert nil))
;                 (println (map count choices))
                 (assert (not-any? empty? choices))
                 (if (seq choices)
                   (apply min-key count choices)
                   #_ (println "is a dead end"))))))
        (env/goal-map sas-problem)))))
;; TODO: assert no top-down.

(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) sol)))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])




;; TODO: cutoff when top-down and bottom-up meet, don't match ? (or earlier)

;; TODO: Take advantage of "greedy-chain" condition, don't assign



;; (do (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util) (require '[angelic.search.action-set.asplan2 :as ap2]))

;; (let [e (force (nth ipc2-logistics 5)) ]  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))))

;; (let [e (make-random-independent-taxi-env 3 3 3 false 1) ]  (println (time (run-counted #(ap/asplan-solution-pair-name (uniform-cost-search (ap/make-asplan-env e ))))))  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))))

;; (let [e (make-random-pairwise-taxi-env 2 2 3 true 1) ]  (println (time (run-counted #(ap/asplan-solution-pair-name (uniform-cost-search (ap/make-asplan-env e ))))))  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))))