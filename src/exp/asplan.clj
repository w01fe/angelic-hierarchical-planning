(ns exp.asplan
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] ]
            [exp [env :as env]  [hierarchy :as hierarchy] 
                 [sas :as sas] [sas-analysis :as sas-analysis]])
  (:import [java.util HashMap]))


; For now, pretend analysis is free, just brute-force it. 

; Put stuff previous in HLAs into state, so we can keep track of, e.g.,
; actions added while accomplishing some other action. 
; For each var, a second var pointing to: pending action, :frozen, or :open
;  This doesn't play with usual state abstraction.
;  Except, we also need to keep track of *user* of frozen far w/o action.

; We have simple, dijkstra-shared-goal options, with same acylic options.

; Can refine until *particular* action resolved, or *any* current action resolved. 
;   (not just any action, steps are too small).

;; TODO: should we allow action to fire even when there is already action scheduled on precond ?

;; TODO: think about variable orderings more.  i.e., in infinite taxi, DAG order is perfect.

;; TODO: also look at using landmarks to structure search ? 
; (but where's the state abstraction?)

; TODO: ideally, we should avoid cyclies in the value of effect-var,
 ; NOT in whole state-abstracted states.

;; NOTE: greedy should come in when we choose a parent for a var. 
; If some parent can use current var RIGHT NOW, should assign to it, not branch.

;; For state abstraction, it would be better to split parent into n+1 booleans:
; (free? v), (parent? v1 v2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

(defn action-var [v]       [:action v])
(defn free-var [v]         [:free? v])
(defn parent-var [v child] [:parent? v child])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a parent (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init child-var-map goal-action]
  (let [vars (env/list-vars init)]
    (env/set-vars init
      (concat 
       (apply concat
         (for [var vars]
           (concat [[(action-var var) nil] [(free-var var) true]]
                   (for [c (child-var-map var)] [(parent-var var c) false]))))
       [[(action-var sas/goal-var-name) goal-action]
        [(free-var sas/goal-var-name) false]]))))

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (let [[evar eval] (util/safe-singleton (seq effect-map))]
    (env/FactoredPrimitive
     [::AddAction name]
     {(action-var evar) nil, evar (precond-map evar), (free-var evar) false}
     {(action-var evar) factored-primitive}
     reward)))


(comment ;; Not actually needed -- use below instead.
  (defn make-fire-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
   (let [[evar eval] (util/safe-singleton (seq effect-map))]
     (env/FactoredPrimitive
      [::Fire name]
      (into precond-map 
            (cons [(action-var evar) factored-primitive]
                  (for [[pvar pval] (dissoc precond-map evar)]
                    [(parent-var pvar evar) true])))
      (into effect-map 
            (cons [(action-var evar) nil]
                  (apply concat
                         (for [[pvar pval] (dissoc precond-map evar)]
                           [[(parent-var pvar evar) false]
                            [(free-var evar) true]]))))
      0))))

(defn make-set-parent-var-action [p-var c-var]
  (env/FactoredPrimitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


; Try to make an action that greedily fires the action scheduled on effect-var,
; effectively representing a composition of set-parent and fire-action actions.
(defn make-greedy-fire-action [s effect-var]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> effect-var action-var (env/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(env/get-var s (free-var %)) precond-vars)]
    (when (and (env/state-matches-map? s precond-map)
               (every? #(env/get-var s (parent-var % effect-var)) unfree-pv))
        (assert (every? #(nil? (env/get-var s (action-var %))) precond-vars))
        (env/FactoredPrimitive
         [::GreedyFire name]
         (into precond-map 
               (concat [[(action-var effect-var) factored-primitive]]
                       (for [v free-pv]   [(free-var v)              true])
                       (for [v unfree-pv] [(parent-var v effect-var) true])))
         (into effect-map 
               (concat [[(action-var effect-var) nil]]
                       (for [v unfree-pv] [(free-var v)              true])
                       (for [v unfree-pv] [(parent-var v effect-var) false])))
         0))))



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

; TODO: take reduced arcs into account, etc.  
(defn activation-actions 
  "Return a list of activation actions for var v, ideally which are supported by 
   current state; i.e., should take reduced arcs into account, etc. "
  [s child-map v]
  (for [c (util/safe-get child-map v)]
    (make-set-parent-var-action v c)))

(defn current-child [s child-var-map p-var]
  (when-not (env/get-var s (free-var p-var))
    (some #(env/get-var s (parent-var p-var %))
          (child-var-map p-var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplest way to express mechanics (in order of preference):

;  Schematics:
;  a* => A   goes to a* -> a   (greedy fire)
;  a => A    goes to  A => A   (bottom-up action)
;  a -> A    goes to  a => A   (bottom-up activate)
;  a => a => goes to => A =>   (top-down action)          
;  a => a -> goes to a => a => (top-down activate)          

; Ideally, should prefer top-most top-down, bottom-most bottom-up, or something...


;; We make this a real type to make accessing precomputed stuff easier...
(deftype ASPlanEnv [init actions-fn g-map]
  env/Env 
    (initial-state [] init)
    (actions-fn    [] actions-fn)
    (goal-fn       [] #(when (env/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [] g-map))

(defn make-asplan-env [sas-problem] 
  (let [causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        child-var-map (util/map-vals #(map second %) (util/group-by first causal-graph))
        vars          (keys (:vars sas-problem))
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (assert (graphs/dag? causal-graph))    
    (ASPlanEnv 
     (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
     (fn asplan-actions [s]
       (let [[aa-vars na-vars] (split-with #(env/get-var s (action-var %)) vars)
             aa-parent-edges   (for [av aa-vars
                                      :let [pm (:precond-map (env/get-var s (action-var av)))]
                                      pv    (remove #{av} (keys pm))
                                      :when (and (not (env/get-var s (action-var pv)))
                                                 (not (= (pm pv) (env/get-var s pv))))]
                                  [pv av])
             na-tuples         (for [nav na-vars
                                     :let  [child (current-child s child-var-map nav)]
                                     :when (and child (not (env/get-var s (action-var child))))]
                                 [nav child])]
        (util/cond-let [x]
          ;; Greedy action -- all preconditions satisfied and not assigned elsewhere
          (some #(make-greedy-fire-action s %) aa-vars) 
            [x]

          ;; Active bottom-up var -- assigned, needs its value changed.               
          (util/find-first (fn [[pv cv]] (env/get-var s (parent-var pv cv))) aa-parent-edges)
            (let [[pv cv] x, 
                  p-val (env/get-var s pv)
                  d-val (util/safe-get-in (env/get-var s (action-var cv)) [:precond-map pv])]
              (apply concat (map (get-in dtgs [pv p-val]) (acyclic-succ-fn pv p-val d-val))))

          ;; Inactive bottom-up var -- needs to be assigned.  
          (first aa-parent-edges)
            (activation-actions s child-var-map (first x))

          ;; Active top-down var -- add actions
          (util/find-first #(not (env/get-var s (free-var %))) (map second na-tuples))  
            (apply concat (vals (util/safe-get-in dtgs [x (env/get-var s x)])))

          ;; Inactive top-down var -- activate it
          (first (map second na-tuples))
            (activation-actions s child-var-map x))))
     (env/goal-map sas-problem))))

(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::GreedyFire) (map env/action-name sol))))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])



;; TODO: cutoff when top-down and bottom-up meet, don't match ? 

;; TODO: Take advantage of "greedy-chain" condition, don't assign


; (use '[exp env hierarchy taxi-infinite ucs asplan hierarchical-incremental-search] 'edu.berkeley.ai.util)
; (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (println (run-counted #(uniform-cost-search e))) (println (run-counted #(asplan-solution-pair-name (debug 0 (sahucs-fast-flat (make-asplan-henv e )))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; First attempt: "Skip" hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; OK, now we need a hierarchy.    Problems:
 ; some of the primitives as-implemented don't play well with state abstraction.
 ; want all derived knowledge to be represented explicitly ? 

; Basic ideas:
 ; In perfect world, store "possible next" set for each var.
  ; When we activate a var, we must either assign to a parent that wants current val (how do we know?),
  ; or choose an action that can lead to a possible next val. 
 ; Also need info going down, maybe?
  ; Maybe we can ignore it for now ...
  ; Can make it last priority to activate var downward, only if we're otherwise stuck.
  ; Still, early deadlock detection is probably important. 

; Now an abstract subproblem should be, either:
 ; (1) achieve a particular precondition of some active action, or 
 ; (2) achieve some precondition of some active action.  
 ; (3) achieve some active action
; advantage of former is simplicity. 
; advantage of latter is faster termination.  
 ; and potentially, more state abstraction?  

; Think about (1) first.  We're in some state, have some active actions and parent commitments, want
; to achieve a particular precondition.  
;  What matters: var and all ancestors, plus all auxillary vars on these.
;  Plus: descenents of ancestors, subject ot some constriants.
;  e.g., same as before.  Not clear what commitments have given us 

; Take a different tack: what we *really* want is maximal state abstraction for each task.
; task termination conditions are, basically, whenever we're about to leave that envelope. 
 ; i.e., could include addition of any downward thing.  


; Idea: if we have both "precondition" and "fire-action" HLAs we cno't need to worry 
; about gg ?!

; We can include just strict ancestors in these things, and let goal be: achieve
; nominal goal, or deadlock.

; Then, we need to be able to recover from deadlock, once we have changed other parts of the world.

; Question: when is this better than, e.g., doing DAG-type thing ? Seems no worse?

; Then, only question is recovery?  Only end up with actions already present if we 
; deadlocked before?  Can just walk back up, it's fine ... but hopefully can detect
; whether deadlock possibly avoided before doing lots of work. 

; One idea: can record "deadlock roots".  i.e., each set parent-var can deadlock a whole subtree.  
; this should really be metadata.  

; Note: what happened to possible-next sets above?  Can use them to filter outside parent-var commitments, once we get up to level where context is apparent.
; What you lose: always have to fully explore var, if it has multiple parents. 




;; TODO: deal with parents that are not relevant.  (i.e., propagate next-sets).




; Note: in "single parent" we should also include tree-reduced situations. 
; Note: in general may be able to improve on precondition context, by taking top-down
;   info into account. ??
; Note: state abstraction not TOO important for achieve-precondition, 
;   since individual steps are still cached in fire-action.

; AddActions, then set-parent-var.   
; Can return either a state where precondition accomplished, or 
; there exist a chain of actions (posisbly empy) leading to a precondition assigned
; outside the context of this precond.  

(comment
 (declare make-fire-action-hla)

; Can either try to achieve a goal val, or use a parent goal val, or both, or neither. ?
; If objective(s) are given, will always return states that satisfy objective(s),
; OR are deadlocked in the process of doing so. 
; If not given, will return all possible values assigned to all parents, (OR deadlock),
; rely on parents to filter.

; Note: nobody actually cares *who* we are deadlocked on, just whether deadlocked outside current set or not ....
(defn make-change-variable-hla [hierarchy var has-goal-val? goal-val goal-action]
  (assert (not (and goal-val goal-action)))
  (let [name [:achieve var goal-val]
        pc   (util/safe-get-in hierarchy [:precond-sets var])]
    (reify :as this
      env/Action
       (action-name [] name)
       (primitive?  [] false)
      env/ContextualAction 
       (precondition-context [s] pc)
      hierarchy/HighLevelAction
       (immediate-refinements- [s]
         (let [cur-val    (env/get-var s var)
               cur-parent (env/get-var s (parent-var var))
               cur-action (env/get-var s (action-var var))]
           (assert (not (= cur-val goal-val)))
           (cond cur-parent
                   [[]]
                 cur-action 
                   [[(make-fire-action-hla hierarchy var cur-action) this]]
                 :else 
                   [[()]]
                 
                 )
           
           )
;         (cond ())
         (if-let [actives (seq (active-action-vars hierarchy s))]
           (if-let [greedy (some #(make-greedy-fire-plan hierarchy s %) actives)]
             [(conj (vec greedy) this)]
             (when-let [open (choose-open-var hierarchy s)]
;  Note; this can cause suboptimalify if someone might want current val.           
;          [[(AddSomeActionHLA hierarchy open) this]]))
               [[(ActivateVarHLA hierarchy open) this]]))
           [[]]))
       (cycle-level-           [s] nil))))



;; Fire a top-down var, or die trying.  
;; ?: we can assume that we have some space in which to use this ?
(defn make-fire-parent-hla [hierarchy var]
  (let [name [:achieve var goal-val]
        pc   (util/safe-get-in hierarchy [:precond-sets var])]
    (reify :as this
      env/Action
       (action-name [] name)
       (primitive?  [] false)
      env/ContextualAction 
       (precondition-context [s] pc)
      hierarchy/HighLevelAction
       (immediate-refinements- [s]
;         (cond ())
         (if-let [actives (seq (active-action-vars hierarchy s))]
           (if-let [greedy (some #(make-greedy-fire-plan hierarchy s %) actives)]
             [(conj (vec greedy) this)]
             (when-let [open (choose-open-var hierarchy s)]
;  Note; this can cause suboptimalify if someone might want current val.           
;          [[(AddSomeActionHLA hierarchy open) this]]))
               [[(ActivateVarHLA hierarchy open) this]]))
           [[]]))
       (cycle-level-           [s] nil))))

; Make HLA that fires current action on var.  
; Note: should try to order preconditions, etc. 
;; Start with fire-action HLA on goal action.
; This should be recursive, since we may have to alternate  between preconditions.  
; Basic idea:
;  Filter out satisfied & deadlocked preconditions
;  (deadlocked = "have a chain of actions leading to an out-pointing parent-var")
;    ??
;  If there are remaining preconditions, choose a "best" one (shallowest?) to satisfy
;  If all satisfied, fire action and return state
;  Otherwise, just return "deadlocked" state.

(defn trivial-precond? 
  "Is this precond trivially satisfied, and not otherwise reserved."
  [s par-var pvar pval]
  (and (= pval         (env/get-var s pvar))
       (#{nil par-var} (env/get-var (parent-var pvar) par-var))
       (nil?           (env/get-var (action-var pvar)))))

;; Is it possible to make this precondition true 
(defn live-precond? 
  "Is is possible to achieve this precond without touching out-of-scope vars?"
  [s par-var pvar pval]
  
  )

(defn best-live-precond 
  "Which of these live var-val preconditions should we achieve first?"
  [s live-preconds]
  
  )

(defn top-down-var
  "Return a var with an inactive parent, that will resolve a deadlock for 
   this action if resolved."
  [s var action]

  )

(defn make-fire-action-hla [hierarchy var action]
  (assert (= var (key (util/safe-singleton (:effect-map action)))))
  (let [name [:fire var]
        pc   (util/safe-get-in hierarchy [:precond-sets var])
        pm   (dissoc (util/safe-get action :precond-map) var)]
    (reify :as this
      env/Action
       (action-name [] name)
       (primitive?  [] false)
      env/ContextualAction 
       (precondition-context [s] pc)
      hierarchy/HighLevelAction
       (immediate-refinements- [s]
         (assert (= (env/get-var s (action-var var)) action))
         (let [[sat unsat] (util/separate (fn [[pvar pval]] (trivial-precond? s var pvar pval)) pm)
               live (filter (fn [[pvar pval]] (live-precond? s var pvar pval)) unsat)]
           (cond-let [x]
             (empty? unsat)
               [(util/make-safe (make-greedy-fire-plan hierarchy s var))]
             (seq live)
               (let [[best-pvar best-pval] (best-live-precond s live)]
                 [[(make-achieve-precondition-hla hierarchy best-pvar best-pval) this]])
             (top-down-var s var action)
               [[(make-fire-parent-hla hierarchy x) this]]
             :else 
               [[]])))   ; Hope parent can resolve problem.  
       (cycle-level-           [s] nil))))


(deftype ASPlanSkipHierarchy [sas-problem vars dtgs child-var-map possible-next-map])

(defn make-asplan-skip-hierarchy [sas-problem dtgs] 
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        child-var-map (util/map-vals #(map second %) (util/group-by first causal-graph))]
    (assert (graphs/dag? causal-graph))
    (ASPlanFlatHierarchy
     sas-problem 
     (keys (:vars sas-problem))
     dtgs
     child-var-map
     (compute-possible-next-map dtgs))))

(defn make-asplan-skip-henv [sas-problem] 
  (let [dtgs (sas-analysis/domain-transition-graphs sas-problem)
        env  (make-asplan-env sas-problem dtgs)]
    (hierarchy/SimpleHierarchicalEnv 
     env
     [(make-fire-action-hla
       (make-asplan-skip-hierarchy sas-problem dtgs) 
       (env/current-context (env/initial-state env)))])))

;; NOTE: where does top-down growing come up in all of this ? 
;  only when everything is deadlocked, AND an available spot.
; ALSO: where does better deadlock detection come in ? 






; end comment
)














(comment ; Version that does not care about target or parent ..
(deftype AddSomeActionHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::AddSomeAction effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] #{effect-var})
  hierarchy/HighLevelAction
   (immediate-refinements- [s] 
     (assert (not (env/get-var s (free-var effect-var))))
     (assert (not (env/get-var s (action-var effect-var))))
     (for [[eval actions] (util/safe-get-in hierarchy [:dtgs effect-var (env/get-var s effect-var)])
           a actions]
       [(make-add-action-action a)]))
   (cycle-level-           [s] nil))
 )

(comment
   ; Stuff from old verion.
  
; Possible-next-map maps from var, val, to var2, to set of vals for var2 that 
; can be used next by an action that changes var, starting at val.

(defn compute-immediate-possible-usage-map [var dtg]
  (util/map-vals
   (fn [nv-actions-map]
     (apply merge-with clojure.set/union 
      (for [actions (vals nv-actions-map)
            a       actions]
        (util/map-vals hash-set (dissoc (:precond-map a) var)))))
   dtg))

(defn compute-edge-necessary-usage-map [var dtg]
  (util/map-vals
   (fn [nv-map]
     (util/map-vals
      (fn [actions]
        (disj (apply clojure.set/intersection (map #(util/keyset (:precond-map %)) actions)) var))
      nv-map))
   dtg))

(defn compute-var-possible-next-map [var dtg]
  (util/map-vals second
   (graphs/quiescence-search
    (for [[sv evm] dtg, ev (keys evm)] [ev sv])
    (fn [v] [v {}])
    (let [blocked-var-map (compute-edge-necessary-usage-map var dtg)]
      (fn update-fn [_ [v old-val] & pred-vals]
        (let [new-val (apply merge-with clojure.set/union
                             (for [[nv incoming-vals] pred-vals]
                               (apply dissoc incoming-vals 
                                      (when-not (= v nv) (util/safe-get-in blocked-var-map [v nv])))))]
          (doseq [v (keys new-val)] (assert (util/subset? (get old-val v #{}) (get new-val v))))
          [v new-val])))
    (for [[v usage-map] (compute-immediate-possible-usage-map var dtg)] [v [v usage-map]]))))

(defn compute-possible-next-map
  "Take domain transition graphs, and compute a nested map 
   variable --> current value --> child variable --> possible-next-child-value,
   where possible-next-child-value is a value for the child variable that could
   possibly be used by a next action that changes variable."
  [dtgs]
  (into {} (for [[var dtg] dtgs] [var (compute-var-possible-next-map var dtg)])))


  ;; TODO: this precludes state abstraction ? 
 (defn can-use-next? [hierarchy use-var use-val user-var user-val]
   (contains? (get-in (:possible-next-map hierarchy) [user-var user-val use-var]) use-val))

 ; Only need vars that could use current val *next* (with support from below, ignore for now).
 (defn possible-parents [hierarchy s effect-var]
   (let [eval (env/get-var s effect-var)]
     (filter
      (fn [p]
        (if-let [pa (env/get-var s (action-var p))]
          (condp = (get (:precond-map pa) effect-var)
            nil  (can-use-next? hierarchy effect-var eval p (get (:effect-map pa) p))
            eval true
            false)
          (can-use-next? hierarchy effect-var eval p (env/get-var s p))))
      ((util/safe-get hierarchy :child-var-map) effect-var)))))