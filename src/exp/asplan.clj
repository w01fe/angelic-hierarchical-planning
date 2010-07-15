(ns exp.asplan
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] ]
            [exp [env :as env]  [hierarchy :as hierarchy] 
                 [sas :as sas] [sas-analysis :as sas-analysis]]))


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
     0)))

(defn make-set-parent-var-action [p-var c-var]
  (env/FactoredPrimitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat Hierarchy HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; TODO: ideally, we should avoid cyclies in the value of effect-var,
 ; NOT in whole state-abstracted states.

;; TODO: add a way to stop, when we reach the right var val. 

;; TODO: make sure top-down setup is right, e.g., we always add a target 
; action, then we can work on the precondition

;; TODO: is there an invariant that whenever a var is "truly active" it 
; has an active var, or is at right val?  If so, we need to enforce this as 
; we activate a top-down var, since it'll appear dead.  


; Simplest way to express mechanics:
;  If any action can greedily fire,
;    fire it.
;  Else, if any vars without actions but with explicit child with action and wrong value,
;    add a directed action.
;  Else, if any vars without actions or explicit children but have child with action,
;    activate precondition
;  Else, if any var without action but with explicit parent, 
;    add an undirected action.

;  Schematics:
;  a => A  goes to  A => A  or a -> a
;  a -> A  goes to  a => A
;  a => a  goes to  a => A
;  A => a  is not allowed ? 



(defn current-child [hierarchy s p-var]
  (some #(env/get-var s (parent-var p-var %))
        (util/safe-get-in hierarchy [:child-var-map p-var])))

(defn possible-next-actions-to [hierarchy var c-val d-val]
  (apply concat 
    (map (util/safe-get-in hierarchy [:dtgs var c-val])
         ((:acyclic-edges-fn hierarchy) var c-val d-val))))

(defn possible-next-actions [hierarchy var c-val]
  (apply concat (vals (util/safe-get-in hierarchy [:dtgs var c-val]))))

; Add any applicable action, using the target val if available.
; If not, goal is to ease deadlock by using a parent.
; TODO: use parent commitments to decide where to head ?

; Ideally, we stop as soon as we've used up at least one parent.
; One idea is just to stop after each action.
; This means we must take care when doing top-down; activation may
; not be required. 
(comment 
(deftype AddSomeActionHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::AddSomeAction effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] 
     (let [cc (util/make-safe (current-child hierarchy s effect-var))]
       #{effect-var (parent-var effect-var cc) (action-var cc)}))
  hierarchy/HighLevelAction
   (immediate-refinements- [s] 
     (assert (not (env/get-var s (action-var effect-var))))
     (let [cc    (util/make-safe (current-child hierarchy s effect-var))
           c-val (env/get-var s effect-var)]
       (if-let [ca (env/get-var s (action-var cc))] ;; driven bottom-up?
         (let [d-val (util/safe-get-in ca :precond-map effect-var)]
           (if (= c-val d-val)
               [[]]) 
             (for [a (possible-next-action-to hierarchy effect-var c-val d-val)]
               [(make-add-action-action a)]))
         (for [a (possible-next-action hierarchy effect-var c-val)]
           [(make-add-action-action a)]))))
   (cycle-level-           [s] nil))
 ;)

; Choose a parent for a var; assumes any greedy vars have already
; fired, so all parents are allowed.  Prereq for adding actions on a var.
(deftype ActivateVarHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::ActivateVar effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] #{})
  hierarchy/HighLevelAction
   (immediate-refinements- [s]
     (assert (env/get-var s (free-var effect-var)))
     (let [asa (AddSomeActionHLA hierarchy effect-var)]
      (for [c (util/safe-get-in hierarchy [:child-var-map effect-var])]
        [(make-set-parent-var-action effect-var c) asa])))
   (cycle-level-           [s] nil))


;; TODO: assert is wrong.?

(defn make-greedy-fire-plan
  "Return an HLA to greedily fire, or nil if cannot greedily fire."
  [hierarchy s effect-var]
  (let [a            (->> effect-var action-var (env/get-var s))
        _            (assert a)
        pm           (:precond-map a)
        precond-vars (keys (dissoc pm effect-var))
        [free-pv unfree-pv] (util/separate #(env/get-var s (free-var %)) precond-vars)]
    (when (and (env/state-matches-map? s pm)
               (every? #(env/get-var s (parent-var % effect-var)) unfree-pv))
      (assert (every? #(nil? (env/get-var s (action-var %))) precond-vars))
      (let [fire (make-fire-action-action a)]
        [(hierarchy/SimpleHLA [::GreedyFire ] 
          (env/precondition-context fire s)
          [(conj (vec (for [p free-pv] (make-set-parent-var-action p effect-var))) 
                 fire
                 (AddSomeActionHLA hierarchy effect-var))])]))))

(defn make-a-greedy-fire-plan [hierarchy s]
  (some #(make-greedy-fire-plan hierarchy s %) 
        (filter #(env/get-var s (action-var %))
                (util/safe-get hierarchy :vars))))


(defn bottom-up-supported-vars [hierarchy s]
  (mapcat (fn [v] 
            (when-let [a (env/get-var s (action-var v))] 
              (for [[var val] (:precond-map a)
                    :when (not (= (env/get-var s var) val))]
                var)))
          (util/safe-get hierarchy :vars)))

(defn top-down-supported-vars [hierarchy s]
  (for [vp (util/safe-get hierarchy :vars)
        vc (util/safe-get-in hierarchy [:child-var-map vp])
        :when (env/get-var s (parent-var vp vc))]
    vc))

(defn choose-open-var 
  "Choose a var to start changing.  Var must be open, i.e. parent-var and action-var both nil.
   Var should be supported, either 
     -from below by open precondition of action on potential parent-var, or
     -from above by parent-var link to this var."
  [hierarchy s]
  (first (filter #(env/get-var s (free-var %)) 
                 (concat (bottom-up-supported-vars hierarchy s)
                         (top-down-supported-vars hierarchy s)))))

(deftype FlatASPlanHLA [hierarchy name pc] :as this
  env/Action
   (action-name [] name)
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] pc)
  hierarchy/HighLevelAction
   (immediate-refinements- [s] 
     (if-let [g (make-a-greedy-fire-plan hierarchy s)] [(conj (vec g) this)]
      (if-let [v (choose-open-var hierarchy s)] [[(ActivateVarHLA hierarchy v) this]] 
        [[]])))
   (cycle-level-           [s] nil))

(defn make-flat-asplan-hla [hierarchy full-context]
  (FlatASPlanHLA hierarchy [::FlatASPlan] full-context))


;;;;;;;;;;;;;;;;;;;;;;;;; Flat Hierarchy precomputations ;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: cutoff when top-down and bottom-up meet, don't match ? 

;; TODO: note, should be able to use acylic dtgs for, e.g., single parent. 

;; TODO: Take advantage of "greedy-chain" condition, don't assign
;   val to parent too high up the chain too early. 

;; Memoized partial computations to speed up acylic edge generation.
(def #^HashMap *forward-reachability-cache* nil)
(def #^HashMap *backward-reachability-cache* nil)

(defn forward-reachable-nodes-and-preds [#^HashMap cache simple-dtgs var-name from-val]
  (util/cache-with cache [:forward var-name from-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (util/safe-get simple-dtgs var-name) from-val)))

(defn backward-reachable-nodes-and-preds [#^HashMap cache simple-dtgs var-name to-val]
  (util/cache-with cache [:backward var-name to-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (map reverse (util/safe-get simple-dtgs var-name)) to-val)))

(defn get-possibly-acyclic-edges
  "Return a list of edges, where those provably on no acyclic s-t path have been eliminated.
   Do so in polynomial time, possibly missing some always-cyclic edges."  
  [cache simple-dtgs var from-val to-val]
  (let [forward-sets  (forward-reachable-nodes-and-preds cache simple-dtgs var from-val)
        backward-sets (backward-reachable-nodes-and-preds cache simple-dtgs var to-val)]
    (filter
     (fn [[a b]]
       (let [f (forward-sets a)
             b (backward-sets b)]
         (and f b (empty? (clojure.set/intersection f b)))))
     (util/safe-get simple-dtgs var))))


(defn get-child-var-map [sas-problem]
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))]
    (assert (graphs/dag? causal-graph))
    (util/map-vals #(map second %) (util/group-by first causal-graph))))

; Cannot be used iwth safe-get...
;(deftype ASPlanFlatHierarchy [sas-problem vars dtgs child-var-map possible-next-map])

(defn make-asplan-env [sas-problem child-var-map dtgs]
  (reify env/Env
   (initial-state [] 
     (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs)))
   (actions-fn    [] :no-actions-fn)
   (goal-fn       [] (env/goal-fn sas-problem))))

(defn make-asplan-flat-henv [sas-problem] 
  (let [child-var-map (get-child-var-map sas-problem)
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        reach-cache   (HashMap.)
        env           (make-asplan-env sas-problem child-var-map dtgs)]
    (hierarchy/SimpleHierarchicalEnv 
     env
     [(make-flat-asplan-hla 
       {:type ASPlanFlatHierarchy
        :sas-problem      sas-problem 
        :vars             (keys (:vars sas-problem))
        :dtgs             dtgs
        :child-var-map    child-var-map
        :acyclic-edges-fn (partial get-possibly-acylic-edges cache simple-dtgs)} 
       (env/current-context (env/initial-state env)))])))

(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) (map env/action-name sol))))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])

; (use '[exp env hierarchy taxi-infinite ucs asplan hierarchical-incremental-search] 'edu.berkeley.ai.util)
; (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (println (run-counted #(uniform-cost-search e))) (println (run-counted #(asplan-solution-pair-name (debug 0 (sahucs-fast-flat (make-asplan-henv e )))))))



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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; First attempt: "Skip" hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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