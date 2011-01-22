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

;; Note: alternative to frozen as implemented here is to
;; necessitate ordering, and make a free-for-all over the (top-down) leavings

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
    (or (util/find-first #(state/get-var s (parent-var p-var %))
                         (child-var-map p-var))
        :out-of-context)))

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


;; TODO: should fail if I own parent, it has right value, but an action. (right now, we assert)...
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
#_    (util/assert-is (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars)
                    "%s" [name precond-map effect-map s])    
    (env-util/make-factored-primitive
     [::Fire name]
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
     0)))

(defn make-sloppy-fire-action [s effect-var]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
        (->> effect-var action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)
        [reserved-pv external-pv] (util/separate #(state/get-var s (parent-var % effect-var))
                                                 unfree-pv)]
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) reserved-pv))
    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var effect-var) factored-primitive]]
                   (for [v free-pv]   [(free-var v)              true])
                   (for [v reserved-pv] [(parent-var v effect-var) true])
                   (for [v external-pv] [(free-var v) false])
                   (for [v external-pv] [(parent-var v effect-var) false])))
     (into effect-map 
           (concat [[(action-var effect-var) nil]]
                   (for [v reserved-pv] [(free-var v)              true])
                   (for [v reserved-pv] [(parent-var v effect-var) false])
                   (for [v reserved-pv] [(action-var v) nil])))
     0)))

(defn make-fire-action-type [s edge-rule effect-var]
  (doto (case edge-rule
          :naive (make-fire-action (->> effect-var action-var (state/get-var s)))
          :greedy (make-greedy-fire-action s effect-var)
          (:sloppy :extra-sloppy) (make-sloppy-fire-action s effect-var))
     #_ (-> (env/applicable? s) assert)))



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
  (apply concat
         (for [v (keys child-map)]
           (let [a (state/get-var s (action-var v))]
             (cond
               (nil? a)      nil
               (= :frozen a) (when-let [c (current-child s child-map v)] [[c v]])
               :else         (remove nil?
                               (for [[p pval] (-> a (util/safe-get :precond-map) (dissoc v))]
                                (let [right-val? (= (state/get-var s p) pval)
                                      p-child    (current-child s child-map p)
                                      unavail?   (not (or (= p-child nil) (= p-child v)))]
                                  (case rule
                                    :naive  (cond unavail?         [p-child v]
                                                  (or (not (= p-child v)) (not (= (state/get-var s (action-var p)) :frozen))) [p v])                                       :greedy (cond unavail?         [p-child v]
                                                  (not right-val?) [p v])
                                    :sloppy (cond (and unavail? (or (not right-val?) (when-let [a (state/get-var s (action-var p))] (not (= a :frozen)))))         [p-child v]
                                                  (and (not unavail?) (not right-val?)) [p v])
                                    :extra-sloppy
                                            (cond (and unavail? (not right-val?)) [p-child v]
                                                  (and (not unavail?) (not right-val?)) [p v]))))))))))




(defn source-vars
  "Take the graph from var-ordering-edges, and return the sources in the same component
   as the goal variable, which are ripe for action.  Returns nil if there are any cycles
   in the graph, since this indicates a deadlock (at least some actions cannot fire)."
  [s child-map check-deadlock? check-components? edge-rule]
;  (println (var-ordering-edges s child-map rule))
  (let [edges (doall (var-ordering-edges s child-map edge-rule))]
    (when (or (not check-deadlock?) (graphs/dag? edges)) 
      (let [sources (clojure.set/difference (set (cons sas/goal-var-name (map first edges))) (set (map second edges)))
            goal-component-sources
            (if check-components?
              (clojure.set/intersection
               sources
               (graphs/ancestor-set (cons [sas/goal-var-name sas/goal-var-name] edges) [sas/goal-var-name]))
              sources)]
        (when-not (= (count sources) (count goal-component-sources)) (println "Warning: multiple components..."))
        (when check-deadlock? (assert (seq goal-component-sources)))
        goal-component-sources))))

(defn source-var-type [s child-map v]
  (let [a (state/get-var s (action-var v))]
    (cond (= a :frozen)  :top-down-activate
          a              :fire

          ;; no action
          (not (state/get-var s (free-var v))) :bottom-up-action 
          (some (fn [c] (when-let [ca (state/get-var s (action-var c))]
                          (contains? (:precond-map ca) v)))
                (child-map v))
                         :bottom-up-activate
          :els           :top-down-action)))

;; TODO: dynamic bottom-up pruning.
 ; i.e., exists precondition of some current action, NOT currently achieved,
 ; that has every child of a parent-link in its ancestor-set. 
; Or, more simply, variables should "die off".  
;; TODO: generalize.  This is just special case for most logistics.
(defn uses-dead-vars? [s ancestor-map child-map extra-edges]
;  false #_
  (let [gpm      (:precond-map (state/get-var s (action-var sas/goal-var-name)))
        live-set (apply clojure.set/union #{sas/goal-var-name}
                        (for [pv (remove #{sas/goal-var-name} (keys gpm))
                              :when (not (= (state/get-var s pv) (gpm pv)))]
                          (ancestor-map pv)))]
    (not-every? live-set
                (concat (map second extra-edges)
                        (for [p (keys child-map)
                              :let [a (state/get-var s (action-var p))]
                              :when (and a (not (= a :frozen)))]
                          p)
                        (for [[p cs] child-map, c cs
                              :when (state/get-var s (parent-var p c))]
                          c)))))


(defn activation-actions  "Return a list of all activation actions for var v"
  [child-map v]
  (for [c (child-map v)]
    (make-set-parent-var-action v c)))

(defn add-actions [s v dtgs]
  (cons (make-freeze-var-action v)
        (for [as (vals (get-in dtgs [v (state/get-var s v)])), a as]
          (make-add-action-action a))))

(defn add-directed-actions [s v dtgs cvm acyclic-succ-fn]
  (let [c-val (state/get-var s v)
        dtg   (get-in dtgs [v c-val])
        child (current-child s cvm v)
        d-val (-> (state/get-var s (action-var child)) :precond-map (get v))]
    ;;    (when greedy? #_ (util/assert-is (not (= c-val d-val)) "%s" (def *s* s)))
    (if d-val 
      (if (= c-val d-val)
        [(make-freeze-var-action v)]
        (for [n-val (acyclic-succ-fn v c-val d-val), a (dtg n-val)]
          (make-add-action-action a)))
      ;; This should only arise in cyclic domains -- TODO: remove?
      (add-actions s v dtgs))))




(comment ; Dead-end check moved out to init.
 (defn possible-activation-actions  
   "Return a list of possible activation actions for var v possible in state s.
   To be possible parent, must be supported from below. "
   [s ancestor-map child-map v]
                                        ;   (activation-actions child-map v) #_   
   (for [c (child-map v) :when (not (or (dead-end? s ancestor-map child-map [[ v c]])))]
     (make-set-parent-var-action v c))))
;   (or (deadlocked? s child-map [[v c]]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ASPlanEnv [base-sas-env init actions actions-fn g-map 
                    ; Following stuff is used by hierarchy.
                      causal-graph dtgs ancestor-var-map child-var-map topological-sort-indices acyclic-succ-fn]
  env/Env 
    (initial-state [e] init)
    (actions-fn    [e] actions-fn)
    (goal-fn       [e] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [e] g-map))

;; TODO: add assertions on precond var = effect var
;; Recall: greedy helps the most when, e.g., lots of passengers and not much room.
(defn make-asplan-env
  "Make an actino-set planning environment.  Switches are:
    check-deadlock?: check for cycles in precedence graph above and beyond lack of sources
    check-components?: check for disconnected components, rule out sources outside of goal comp
    edge-rule: :naive, :greedy, :sloppy, or :extra-sloppy.
       Naive means we stick exactly to the simple semantics of the vanilla actions.
       Greedy means we forget about reserving preconditions when free and we can fire right now (less branching).
       Sloppy means we ignore if preconditions are free, but require no action on them.
       Extra-sloppy means anything goes -- if you can execute ignoring commitments, go for it."
  ([sas-problem & {:keys [directed? greedy? deadlock? dead-vars? components?] :as m
                   :or   {directed? true greedy? true deadlock? true dead-vars? true components? false}}]
     (assert (every? #{:directed? :greedy? :deadlock? :dead-vars? :components?} (keys m)))
     (let [edge-rule     (if greedy? :greedy :naive)
           causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
           vars          (graphs/ancestor-set causal-graph [sas/goal-var-name])
           causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
           tsi           (graphs/topological-sort-indices causal-graph)
           av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
           child-var-map (assoc (util/map-vals #(map second %) (group-by first causal-graph))
                           sas/goal-var-name [])
                                        ;        vars          (keys (:vars sas-problem))
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
           acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
;       (assert (graphs/dag? causal-graph))    
       (assert (sas-analysis/unary? sas-problem))
       
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
        (concat
         (for [v vars] (make-freeze-var-action v))
         (for [a (:actions sas-problem)] (make-add-action-action a))
         (for [[p cs] child-var-map, c cs] (make-set-parent-var-action p c))
         (for [a (:actions sas-problem)] (make-fire-action a)))

        (fn asplan-actions [s]
          (when-let [sources (and (or (not dead-vars?) (not (uses-dead-vars? s av-map child-var-map []))) 
                                  (seq (source-vars s child-var-map deadlock? components? edge-rule)))]
            (let [sources-by-type (group-by #(source-var-type s child-var-map %) sources)]
;;              (println sources-by-type)
              (util/cond-let [sources]
                (seq (sources-by-type :fire))
                [(make-fire-action-type s  edge-rule (first sources))]

                (seq (sources-by-type :bottom-up-action))
                (if directed?
                  (add-directed-actions s (apply min-key tsi sources) dtgs child-var-map acyclic-succ-fn)
                  (add-actions s (apply min-key tsi sources) dtgs))               
                     
                (seq (sources-by-type :bottom-up-activate))
                (activation-actions child-var-map (apply max-key tsi sources)) ;; TODO: smarter sort!
                
                (seq (sources-by-type :top-down-activate))
                (do (println "I!") (activation-actions child-var-map (first sources)))
                
                (seq (sources-by-type :top-down-action))
                (do (println "A!") (add-actions s (first sources) dtgs))
                
                :else (assert "Unknown source type!")))))
        (env/goal-map sas-problem)
        causal-graph dtgs av-map child-var-map tsi acyclic-succ-fn))))

(comment
  (try [(make-fire-action-type s  edge-rule (first sources))] ;; TODO: rempve!
                              (catch AssertionError e nil)))

(defn make-naive-asplan-env
  "Replace the actions-fn in asplan-env with one that generates all legal actions,
   with no partitioning or pruning."
  [sas-problem]
  (let [e (make-asplan-env sas-problem)]
    (assoc e :actions-fn (sas/make-simple-successor-generator (keys (:init e)) (:actions e)))))


(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) sol)))

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



;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'edu.berkeley.ai.util 'angelic.sas.hm-heuristic)

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


 ; (doseq [[alg sp]  [[make-asplan-env asplan-solution-pair-name] [angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name]] ] (println (time (run-counted #(sp (uniform-cost-search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))

; (-> (nth (vals (sas-sample-files 1)) 5) make-sas-problem-from-pddl unarize make-asplan-env interactive-search)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; First attempt: "Skip" hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; OK, now we need a hierarchy.    Problems:
 ; some of the primitives as-implemented don't play well with state abstraction.
 ; want all derived knowledge to be represented explicitly ? 

; Now an abstract subproblem should be, either:
 ; (1) achieve a particular precondition of some active action, or 
 ; (2) achieve some precondition of some active action.  
 ; (3) achieve some active action




;; Can tell a number of things here:
;; If :out-of-context is a source, we're ooc-deadlocked.
;; If we have a cycle after dropping :ooc edges, we're real deadlocked.
;; Right now we do lots of redundant checking rather than passing around state
;; Better for state abstractino, I guess.
;; Stick to that for now.  


(defn restricted-source-vars
  "Like get-sources, but take a sink-var that restricts the context
   Will either return
     (1) :deadlocked, if the state is truly deadlocked (within current context)
     (2) :blocked, if the state is blocked on something out of context
     (3) a non-empty list of sources, when neither of the above is true."
  [s hierarchy sink-var edge-rule]
  (let [restricted-cvm (util/safe-get-in hierarchy [:restricted-cvms sink-var])
        edges          (var-ordering-edges s restricted-cvm edge-rule)
        [ooc-edges context-edges] (util/separate (fn [[s t]] (= s :out-of-context)) edges)]
;    (println "\n"  (state/as-map s) "\n" restricted-cvm sink-var ooc-edges context-edges "\n")
    (cond (not (graphs/dag? context-edges)) :deadlocked
          (seq ooc-edges)                   :blocked
          :else           (clojure.set/difference (set (cons sink-var (map first context-edges)))
                                                  (set (map second context-edges))))))


(declare make-fire-action-hla)

(defn make-achieve-precondition-hla [hierarchy var dst-val]
  (let [name [:achieve-precondition var dst-val]
        av   (action-var var)
        pc   (util/safe-get-in hierarchy [:precondition-context-map var])
;        pc   (:full-context hierarchy)
        ]
    (reify
      env/Action
       (action-name [a] name)
       (primitive?  [a] false)
      env/ContextualAction 
       (precondition-context [a s] pc)
      hierarchy/HighLevelAction
       (immediate-refinements- [this s] 
         (cond (= (state/get-var s var) dst-val)
                 (do ;(print "!S") (flush)
                   (assert (not (when-let [a (state/get-var s av)] (not (= a :frozen))))) [[]])
               (state/get-var s av)
                 (case (restricted-source-vars s hierarchy var :greedy)
                   :deadlocked []
                   :blocked    [[]]
                   [[(make-fire-action-hla hierarchy var (state/get-var s av)) this]])                 
               :else 
                 (let [p-val (state/get-var s var)
                       dtg   (util/safe-get-in hierarchy [:dtgs var p-val])]
                   ;(print "!C")
                   (for [n-val ((:acyclic-succ-fn hierarchy) var p-val dst-val), a (dtg n-val)]
                     [(make-add-action-action a) this]))))
       (cycle-level-           [a s] nil))))





(defn make-fire-action-hla  [hierarchy effect-var a]
  (let [name          [:fire-action effect-var]
        reduced-pm    (dissoc (:precond-map a) effect-var)
        ancestor-vars (util/safe-get-in hierarchy [:ancestor-var-map effect-var])
        child-var-map (:child-var-map hierarchy)
        pc (into #{(action-var effect-var)}
                 (apply concat
                        (for [v (distinct (apply concat (for [p (keys reduced-pm)] (util/safe-get-in hierarchy [:ancestor-var-map p]))))]
                          (concat 
                           [v (free-var v) (action-var v)]
                           (for [c (child-var-map v) :when (ancestor-vars c)] (parent-var v c))))))]
;    (println "FA" name pc "\n" (clojure.set/difference (:full-context hierarchy) pc))
  (reify
    env/Action
      (action-name [a] name)
      (primitive?  [a] false)
    env/ContextualAction 
      (precondition-context [a s] pc) ;; perhaps can do better?
    hierarchy/HighLevelAction
    (immediate-refinements- [this s]
;                            (println (state/as-map s))
;        (Thread/sleep 10)
      
      (assert (= (state/get-var s (action-var effect-var)) a))
     #_ (println "REF!" effect-var)
      (let [source-vars (restricted-source-vars s hierarchy effect-var :greedy)]
        (case source-vars
          :deadlocked (do #_(println "D!") [])
          :blocked    (do #_(println "B!") [[]])
          (if (contains? source-vars effect-var) ; Fire directly
            [[(make-greedy-fire-action s effect-var)]]
            (util/cond-let [p]
              (util/find-first ; Achieve existing precondition
               #(and (state/get-var s (parent-var % effect-var))
                     (not (= (state/get-var s %) (reduced-pm %)))
                     (not (keyword? (restricted-source-vars s hierarchy % :greedy) #_(util/prln  % "SV"))))
               (sort-by (comp + (:topological-sort-indices hierarchy)) (keys reduced-pm)))
              (do #_(println "BA!") [[(make-achieve-precondition-hla hierarchy p (reduced-pm p)) this]])

              (util/find-first #(and (state/get-var s (free-var %)) ; Activate existing precondition
                                     (not (= (state/get-var s %) (reduced-pm %))))
                               (keys reduced-pm))
              (do #_(println "BP!") (for [a (activation-actions child-var-map p)] [a this]))
                
              :else ; Top-down nonsense
              (let [sources-by-type (group-by #(source-var-type s child-var-map %) source-vars)]
                (util/cond-let [sources]
                  (seq (sources-by-type :top-down-activate))
                  (let [v (first sources)]
                    (println "TP!" v)
                    (for [a (activation-actions child-var-map v)]
                      [a this]))
                
                  (seq (sources-by-type :top-down-action))
                  (let [v (first sources)]
                    (println "TA!" v) ;  (state/get-var s x) (state/get-var s (parent-var x sas/goal-var-name))
                    (for [a (cons (make-freeze-var-action v)
                                  (for [as (vals (get-in hierarchy [:dtgs v (state/get-var s v)])), a as]
                                    (make-add-action-action a)))]
                      [a this]))
                
                  :else (assert "Nothing to do"))))))))
       (cycle-level-           [a s] nil))))


;(def *bs* nil)

 ; include ancestor vars, action vars, free vars, in-pointing 'rents
(defn make-asplan-skip-henv [sas-problem] 
  (let [env    (make-asplan-env sas-problem)
        cg     (:causal-graph env)
        cvm    (:child-var-map env)
        av-map (:ancestor-var-map env)
        pc-map (into {} 
                 (for [[k as] av-map] 
                   [k 
                    (into as
                     (concat
                      (for [v as] (free-var v))
                      (for [v as] (action-var v))
                      (for [v as, c (cvm v), :when (as c)] (parent-var v c))))]))
        fa-map (into {} 
                 (for [[k as] av-map] 
                   [k 
                    (into as
                     (concat
                      (for [v as] (free-var v))
                      (for [v as] (action-var v))
                      (for [v as, c (cvm v)] (parent-var v c))))]))
        ]
 ;    (println "\n" av-map "\n\n" pc-map)
    (hierarchy-util/make-simple-hierarchical-env 
     env
     [(make-fire-action-hla
       {:type                     ::ASPlanSkipHierarchy
        :full-context             (state/current-context (env/initial-state env))
        :dtgs                     (:dtgs env)
        :child-var-map            cvm
        :restricted-cvms          (into {}
                                        (for [sink (av-map sas/goal-var-name)
                                              :let [ancestors (util/safe-get av-map sink)]]
                                          [sink (util/map-vals #(filter ancestors  %) (select-keys cvm ancestors))]))        
        :ancestor-var-map         av-map
        :acyclic-succ-fn          (:acyclic-succ-fn env)
        :topological-sort-indices (:topological-sort-indices env)
        :precondition-context-map pc-map
        :fire-action-pc-map       fa-map}
       sas/goal-var-name
       (state/get-var (env/initial-state env) (action-var sas/goal-var-name)))])))


(defn asplan-skip-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) (map env/action-name sol))))

(defn asplan-skip-solution-pair-name [[sol rew]]
  [(asplan-skip-solution-name sol) rew])



;; TODO: faster & early deadlock detection.
;; TODO: detect "out-of-context" deadlock, fail immediately.
;; TODO: precond ordering when we activate (handled by activation-actions?)

;; (use 'angelic.search.explicit.hierarchical)

;; (doseq [[alg sp search]  [[make-asplan-env asplan-solution-pair-name uniform-cost-search] [make-asplan-skip-henv asplan-skip-solution-pair-name dsh-ucs-inverted]] ] (println (time (run-counted #(sp (search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))

;; (doseq [[alg sp search]  [[angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name uniform-cost-search] [angelic.search.action-set.asplan-broken/make-asplan-skip-henv angelic.search.action-set.asplan-broken/asplan-skip-solution-pair-name dsh-ucs-inverted]] ] (println (time (run-counted #(sp (search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))



;; TODO: (let [e (make-random-infinite-taxi-sas2 3 2 5 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e)))))))) gives bad results; replacing inverted iwht regular fixes it ... ?

;; minimal exmaple:
;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 1 2 i)] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e)))))))))

;  (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))

; (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (interactive-hierarchical-search (make-asplan-skip-henv e)))

; (let [e (make-random-infinite-taxi-sas2 2 2 2 2)] (interactive-hierarchical-search (make-asplan-skip-henv e)))

; (let [e (force (nth ipc2-logistics 0))] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))



;(let [e (make-random-infinite-taxi-sas2 5 5 5 1) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))   (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))




(comment
 ;; Like above, but tests actinos rather than asserting..
 (defn make-greedy-fire-action-h [s effect-var]
   (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
         (->> effect-var action-var (state/get-var s))
         precond-vars (keys (dissoc precond-map effect-var))
         [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
     (when (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars)
       (let [a (env-util/make-factored-primitive
                [::Fire name]
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
                0)]
         (when (env/applicable? a s) a))))))

(comment 
;; TODO: these are too restrictive!  They'll say an action is deadlocked even
; when one precondition is just waiting on another.
  (declare precond-deadlocked?)
  (defn action-deadlocked? [s var]
    (when-let [a (state/get-var s (action-var var))]
      (when-not (= a :frozen)
        (some #(precond-deadlocked? s % var) (remove #{var} (keys (:precond-map a)))))))

  (defn precond-deadlocked? [s precond e-var]
    (or (and (not (state/get-var s (free-var precond)))
             (not (state/get-var s (parent-var precond e-var))))
        (action-deadlocked? s precond)))

  (defn precond-deadlocked-ooc? [s precond e-var child-var-map context]
    (or (and (not (state/get-var s (free-var precond)))
             (not (state/get-var s (parent-var precond e-var)))
             (not (contains? context (current-child s child-var-map precond))))
        (when-let [a (state/get-var s (action-var precond))]
          (when-not (= a :frozen)
            (some #(precond-deadlocked-ooc? s % precond child-var-map context) 
                  (remove #{precond} (keys (:precond-map a)))))))))