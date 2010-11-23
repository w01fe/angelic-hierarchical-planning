(ns angelic.search.action-set.asplan
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis])
  (:import [java.util HashMap]))


;; Fixed version.

; For now, pretend analysis is free, just brute-force it. 

; Put stuff previous in HLAs into state, so we can keep track of, e.g.,
; actions added while accomplishing some other action. 
; For each var, a second var pointing to: pending action, :frozen, or :open
;  This doesn't play with usual state abstraction.
;  Except, we also need to keep track of *user* of frozen far w/o action.

; We have simple, dijkstra-shared-goal options, with same acylic options.

; Can refine until *particular* action resolved, or *any* current action resolved. 
;   (not just any action, steps are too small).

;; TODO: think about variable orderings more.  i.e., in infinite taxi, DAG order is perfect.

;; TODO: also look at using landmarks to structure search ? 
; (but where's the state abstraction?)

; TODO: ideally, we should avoid cyclies in the value of effect-var,
 ; NOT in whole state-abstracted states.

;; NOTE: greedy should come in when we choose a parent for a var. 
; If some parent can use current var RIGHT NOW, should assign to it, not branch.
 ; Except, greedy actions takes care of this.

;; For state abstraction, split parent into n+1 booleans: (free? v), (parent? v1 v2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

;; Action vars have a special value, :frozen, meaning that current value must be used
;; by child.  Only really useful 
(defn action-var [v]       [:action v])
(defn free-var [v]         [:free? v])
(defn parent-var [v child] [:parent? v child])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a child (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init child-var-map goal-action]
  (let [vars (state/list-vars init)]
    (state/set-vars init
      (concat 
       (apply concat
         (for [var vars]
           (concat [[(action-var var) nil] [(free-var var) true]]
                   (for [c (child-var-map var)] [(parent-var var c) false]))))
       [[(action-var sas/goal-var-name) goal-action]]))))

(defn current-child [s child-var-map p-var]
  (when-not (state/get-var s (free-var p-var))
    (util/find-first #(state/get-var s (parent-var p-var %))
      (child-var-map p-var))))

(def *add-count* (util/sref 0))


(defn make-freeze-var-action [evar]
  (env-util/make-factored-primitive
     [::FreezeVar evar]
     {(action-var evar) nil}
     {(action-var evar) :frozen}
     0))

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (util/sref-set! *add-count* (inc (util/sref-get *add-count*)))
  (let [[evar eval] (util/safe-singleton (seq effect-map))]
    (env-util/make-factored-primitive
     [::AddAction name]
     {(action-var evar) nil, evar (precond-map evar)}
     {(action-var evar) factored-primitive}
     reward)))

(defn make-set-parent-var-action [p-var c-var]
  (env-util/make-factored-primitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


(defn make-fire-action
  "Simple version of greedy-fire, used for exhaustive action list. (No add-parent)."
  [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (let [effect-var (key (util/safe-singleton (seq effect-map)))
        precond-vars (keys (dissoc precond-map effect-var))]
    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var effect-var) factored-primitive]]
                   (for [v precond-vars] [(parent-var v effect-var) true])
                   (for [v precond-vars] [(action-var v) :frozen])))
     (into effect-map 
           (concat [[(action-var effect-var) nil]]
                   (for [v precond-vars] [(free-var v)              true])
                   (for [v precond-vars] [(parent-var v effect-var) false])
                   (for [v precond-vars] [(action-var v) nil])))
     0)))


;; Try to make an action that greedily fires the action scheduled on effect-var,
;; effectively representing a composition of set-parent and fire-action actions.
;; Note that this avoids some (unnecessary) branching on children of parent vars.
;; Assumes this will always be called on a "source", and asserts correspondingly.
(defn make-greedy-fire-action [s effect-var]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> effect-var action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars))
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) unfree-pv))
    (doto (env-util/make-factored-primitive
           [::GreedyFire name]
           (into precond-map 
                 (concat [[(action-var effect-var) factored-primitive]]
                         (for [v free-pv]   [(free-var v)              true])
                         (for [v unfree-pv] [(parent-var v effect-var) true])
                         (for [v precond-vars] [(action-var v) (state/get-var s (action-var v))])))           
           (into effect-map 
                 (concat [[(action-var effect-var) nil]]
                         (for [v unfree-pv] [(free-var v)              true])
                         (for [v unfree-pv] [(parent-var v effect-var) false])
                         (for [v precond-vars] [(action-var v) nil])))
           0)
      (-> (env/applicable? s) assert))))


;; TODO: sloppy (var can be reserved for someone else, no action),
;;       extra-sloppy (if it has the right value now, who cares about anything else?)

;; TODO: should fail if I own parent, it has right value, but an action. (right now, we assert)...

(comment ;; Version of above that allows "stealing"
 (defn make-greedy-fire-action [s effect-var]
   (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
         (->> effect-var action-var (state/get-var s))
         precond-vars (keys (dissoc precond-map effect-var))
         [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)
         [reserved-pv external-pv] (util/separate #(state/get-var s (parent-var % effect-var))
                                                  unfree-pv)]
     (when (state/state-matches-map? s precond-map)
       (env-util/make-factored-primitive
        [::GreedyFire name]
        (into precond-map 
              (concat [[(action-var effect-var) factored-primitive]]
                      (for [v free-pv]   [(free-var v)              true])
                      (for [v reserved-pv] [(parent-var v effect-var) true])
                      (for [v external-pv] [(free-var v) false])
                      (for [v external-pv] [(parent-var v effect-var) false])))
        (into effect-map 
              (concat [[(action-var effect-var) nil]]
                      (for [v reserved-pv] [(free-var v)              true])
                      (for [v reserved-pv] [(parent-var v effect-var) false])))
        0)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitive Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn backward-reachable-nodes-and-preds [#^HashMap cache simple-dtgs var-name to-val]
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


(defn activation-actions  "Return a list of all activation actions for var v"
  [child-map v]
  (for [c (child-map v)]
    (make-set-parent-var-action v c)))


;; TODO: generalize to modes other than greedy.
(defn var-ordering-edges
  "Construct a graph on the state variables, where an edge from s --> t means
   'something must happen at s for the action at t to go away', more or less.

   Specifically, we have the following kinds of edges:
    (1)                  If (= (action-var v) :frozen), child(v)!=nil, child(v) -->  v
    (2)(a) naive:        If (action-var c) has precondition on p, (not owned or not frozen) and not reserved elsewhere, p --> c
    (2)(b) greedy etc.:  If (action-var c) has precondition on p, value mismatch and not reserved elsewhere, p --> c
    (3)(a) naive+greedy: If (action-var c) has precondition on p, reserved by o!=c, o --> c
    (3)(b) sloppy:       If (action-var c) has precondition on p, value mismatch or action on p and reserved by o!=c, o --> c
    (3)(c) extra-sloppy: If (action-var c) has precondition on p, value mismatch and reserved by o!=c, o --> c"   
  [s child-map rule]
  (assert (contains? #{:naive :greedy :sloppy :extra-sloppy} rule))
  (assert (contains? #{:greedy} rule))  
  (apply concat
         (for [v (cons sas/goal-var-name (keys child-map))]
           (let [a (state/get-var s (action-var v))]
             (cond
               (nil? a)      nil
               (= :frozen a) (when-let [c (current-child s child-map v)] [[c v]])
               :else         (remove nil?
                               (for [[p pval] (-> a (util/safe-get :precond-map) (dissoc v))]
                                (let [right-val? (= (state/get-var s p) pval)
                                      p-child    (current-child s child-map p)
                                      unavail?   (not (or (= p-child nil) (= p-child v)))]
                                  (cond unavail?         [p-child v]
                                        (not right-val?) [p v])))))))))

;; TO remove deadlock, simply avoid dag check and remove assert.
(defn source-vars
  "Take the graph from var-ordering-edges, and return the sources in the same component
   as the goal variable, which are ripe for action.  Returns nil if there are any cycles
   in the graph, since this indicates a deadlock (at least some actions cannot fire)."
  [s child-map rule]
;  (println (var-ordering-edges s child-map rule))
  (let [edges (var-ordering-edges s child-map rule)]
    (when (graphs/dag? edges)
      (let [sources (clojure.set/difference (set (cons sas/goal-var-name (map first edges))) (set (map second edges)))
            goal-component (graphs/ancestor-set (cons [sas/goal-var-name sas/goal-var-name] edges) [sas/goal-var-name])
            goal-component-sources (clojure.set/intersection sources goal-component)]
        (when-not (= (count sources) (count goal-component-sources)) (println "Warning: multiple components..."))
        (assert (seq goal-component-sources))
        goal-component-sources))))

(defn source-var-type [s child-map v]
  (let [a (state/get-var s (action-var v))]
    (cond (= a :frozen)
          :top-down-activate

          a
          :fire

          ;; no action
          (not (state/get-var s (free-var v)))
          :bottom-up-action ;; Can assert on action below...

          (some (fn [c] (when-let [ca (state/get-var s (action-var c))]
                          (contains? (:precond-map ca) v)))
                (child-map v))
          :bottom-up-activate

          :else
          :top-down-action)))

;; TODO: dynamic bottom-up pruning.
 ; i.e., exists precondition of some current action, NOT currently achieved,
 ; that has every child of a parent-link in its ancestor-set. 
; Or, more simply, variables should "die off".  
;; TODO: generalize.  This is just special case for most logistics.
(defn dead-end? [s ancestor-map child-map extra-edges]
;  false #_
  (let [gpm      (:precond-map (state/get-var s (action-var sas/goal-var-name)))
        live-set (apply clojure.set/union #{sas/goal-var-name}
                        (for [pv (remove #{sas/goal-var-name} (keys gpm))
                              :when (not (= (state/get-var s pv) (gpm pv)))]
                          (ancestor-map pv)))]
    (not-every? live-set
                (concat (map second extra-edges)
                        (for [[p cs] child-map, c cs
                              :when (or (state/get-var s (parent-var p c))
                                        (state/get-var s (action-var c)))]
                          c)))))


;; Why can we use parent-edges and not filtered res-edges???
(defn b-deadlocked? [s child-map extra-edges]
;  false #_
  (let [parent-edges (concat extra-edges 
                       (for [[p cs] child-map, c cs :when (state/get-var s (parent-var p c))] [p c]))
        ;; Parent->child actions for active PC, where action on child actually wants parent
        ; ? =*=> A
        res-map      (into {} (filter (fn [[p c]] 
                                        (when-let [a (state/get-var s (action-var c))]
                                          (contains? (:precond-map a) p))) 
                                      parent-edges))

        ; Cross-edge -- from var reserving precondition to other var needing it.
        extra-edges  (for [[p c] parent-edges 
                           :let [a (state/get-var s (action-var p))] 
                           :when a
                           precond (remove #{p} (keys (:precond-map a)))
                           :let [res (res-map precond)]
                           :when res]
                       [res p])]
    (not (graphs/dag? (concat parent-edges extra-edges)))))

(defn possible-activation-actions  
   "Return a list of possible activation actions for var v possible in state s.
   To be possible parent, must be supported from below. "
   [s ancestor-map child-map v]
;   (activation-actions child-map v) #_   
   (for [c (child-map v) :when (not (or #_ (b-deadlocked? s child-map [[v c]])
                                        (dead-end? s ancestor-map child-map [[ v c]])))]
     (make-set-parent-var-action v c)))
;   (or (deadlocked? s child-map [[v c]]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplest way to express mechanics (in order of preference):

;  Schematics:
;  a* => A   goes to a* -> a   (greedy fire)
;  a => A    goes to  A => A   (bottom-up action)
;  a -> A    goes to  a => A   (bottom-up activate)
;  a => a => goes to => A =>   (top-down action)          
;  a => a -> goes to a => a => (top-down activate)          

; Ideally, should prefer top-most top-down, bottom-most bottom-up, or something...

(defrecord ASPlanEnv [base-sas-env init actions actions-fn g-map 
                    ; Following stuff is used by hierarchy.
                      causal-graph dtgs ancestor-var-map child-var-map acyclic-succ-fn]
  env/Env 
    (initial-state [e] init)
    (actions-fn    [e] actions-fn)
    (goal-fn       [e] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [e] g-map))

(defn make-asplan-env [sas-problem] 
  (def *add-count* (util/sref 0))
  (let [causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        vars          (graphs/ancestor-set causal-graph [sas/goal-var-name])
        causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
        tsi           (graphs/topological-sort-indices causal-graph)
        av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
        child-var-map (util/map-vals #(map second %) (group-by first causal-graph))
;        vars          (keys (:vars sas-problem))
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (assert (graphs/dag? causal-graph))    
;    (clojure.inspector/inspect-tree child-var-map)
    (ASPlanEnv.
     sas-problem
     (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
     (concat
      (for [v vars] (make-freeze-var-action v))
      (for [a (:actions sas-problem)] (make-add-action-action a))
      (for [[p cs] child-var-map, c cs] (make-set-parent-var-action p c))
      (for [a (:actions sas-problem)] (make-fire-action a)))

     (fn asplan-actions [s]
;;       (println "\n" s)
       (when-let [sources (and (not (dead-end? s av-map child-var-map [])) ;; This is necessary to catch hanging edges, or need other checks.  i.e., look at top-down env.
                               (seq (source-vars s child-var-map :greedy)))]
         (let [sources-by-type (group-by #(source-var-type s child-var-map %) sources)]
;           (println sources-by-type)
           (util/cond-let [sources]
             (seq (sources-by-type :fire))
             [(make-greedy-fire-action s (first sources))]

             (seq (sources-by-type :bottom-up-action))
             (let [v     (apply min-key tsi sources)
                   c-val (state/get-var s v)
                   dtg   (get-in dtgs [v c-val])
                   child (current-child s child-var-map v)
                   d-val (-> (state/get-var s (action-var child)) :precond-map (util/safe-get v))]
               (util/assert-is (not (= c-val d-val)) "%s" (def *s* s)) ;; TODO: this only correct for greedy...
               (for [n-val (acyclic-succ-fn v c-val d-val), a (dtg n-val)]
                (make-add-action-action a)))               

             (seq (sources-by-type :bottom-up-activate))
             (possible-activation-actions s av-map child-var-map (apply max-key tsi sources)) ;; TODO: sort!

             (seq (sources-by-type :top-down-activate))
             (let [v (first sources)]
               (println "I!" v)
               (possible-activation-actions s av-map child-var-map (first sources))) ;; TODO: sort?

             (seq (sources-by-type :top-down-action))
             (let [v (first sources)]
               (println "A!" v) ;                         (state/get-var s x) (state/get-var s (parent-var x sas/goal-var-name))
               (cons (make-freeze-var-action v)
                     (for [as (vals (get-in dtgs [v (state/get-var s v)])), a as]
                       (make-add-action-action a))))
               
             :else (assert "Unknown source type!")))))
     (env/goal-map sas-problem)
     causal-graph dtgs av-map child-var-map acyclic-succ-fn)))

(defn make-naive-asplan-env
  "Replace the actions-fn in asplan-env with one that generates all legal actions,
   with no partitioning or pruning."
  [sas-problem]
  (let [e (make-asplan-env sas-problem)]
    (assoc e :actions-fn (sas/make-simple-successor-generator (keys (:init e)) (:actions e)))))


(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::GreedyFire) sol)))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])

(defn unrealized-reward [s]
  (->> (state/as-map s)
       (filter #(= (first (key %)) :action))
       (keep val)
       (map :reward)
       (apply +)))


(comment 
 (defn augmented-actions-and-goal-pair
   "Return a set of actions and goal vv-pair that takes canceling of existing
   commitments into account -- should really be incorporated into above?"
   [asplan-env]
   (let [init (env/initial-state asplan-env)
         goal-var [::asplan-goal :?]
         goal-val [::asplan-goal :true]]
     [(cons
       (env-util/make-factored-primitive
        [::asplan-goal-action]
        (into {sas/goal-var-name sas/goal-true-val}
              (for [var (filter #(#{:action :free? :parent?} (first %)) (keys init))]
                [var (case (first var) :free? true :parent? false :action nil)]))
        {goal-var goal-val}
        0)
       (:actions asplan-env))
      [goal-var goal-val]])))


;; TODO: cutoff when top-down and bottom-up meet, don't match ? (or earlier)

;; TODO: Take advantage of "greedy-chain" condition, don't assign



;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'edu.berkeley.ai.util 'angelic.sas.hm-heuristic)

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


; (doseq [[alg sp]  [[make-asplan-env asplan-solution-pair-name] [angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name]] ] (println (time (run-counted #(sp (uniform-cost-search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))