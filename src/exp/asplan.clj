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
;  Instead, can have var-in-use, var-action, latter always nil if not in-use.
;    This allows us to abstract away action if we want.  
;    Annoying: we now have to have primitives for changing this extra state. 
;  Except, we also need to keep track of *user* of frozen far w/o action.



; Question: do we additionally need to keep token to guide refs?

; We have simple, dijkstra-shared-goal options, with same acylic options.

; Can refine until *particular* action resolved, or *any* current action resolved. 
;   (not just any action, steps are too small).


;; TODO: should we allow action to fire even when there is already action scheduled on precond ?

;; TODO: think about variable orderings more.  i.e., in infinite taxi, DAG order is perfect.


;; TODO: also look at using landmarks to structure search ? 
; (but where's the state abstraction?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Types, Protocols, Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

(defn action-var [v] ['action v])
(defn parent-var [v] ['parent v])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can have an active action
   (which changes only that var), OR a parent (in which case it must eventually be used
   to fire an active action on that var), OR neither (but not both), in which case it
   is open."
  [init goal-action]
  (let [vars (env/list-vars init)]
    (env/set-var 
     (env/set-vars init
                   (concat (for [var vars] [(action-var var) nil])
                           (for [var vars] [(parent-var var) nil])))
     (action-var sas/goal-var-name) goal-action)))

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (let [[evar eval] (util/safe-singleton (seq effect-map))]
    (env/FactoredPrimitive
     [::Add name]
     {; (parent-var evar) nil  ;skip this for efficiency ...
      (action-var evar) nil evar (precond-map evar)}
     {(action-var evar) factored-primitive}
     reward)))

; Here, is question of if we *require* reservations or not.
 ; You *must* have them, or you may cancel other reservations, bye correctness.
(defn make-fire-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (let [[evar eval] (util/safe-singleton (seq effect-map))]
    (env/FactoredPrimitive
     [::Fire name]
     (into precond-map 
           (cons [(action-var evar) factored-primitive]
                 (for [[pvar pval] (dissoc precond-map evar)]
                   [(parent-var pvar) evar])))
     (into effect-map 
           (cons [(action-var evar) nil]
                 (for [[pvar pval] precond-map]
                   [(parent-var pvar) nil])))
     0)))

(defn make-set-parent-var-action [p-var new-parent]
  (env/FactoredPrimitive 
   [::SetParent p-var new-parent] 
   {(parent-var p-var) nil} 
   {(parent-var p-var) new-parent} 
   0))

(declare ActivateVarHLA)

(defn make-greedy-fire-plan
  "Return an HLA to greedily fire, or nil if cannot greedily fire."
  [hierarchy s effect-var]
  (let [a  (->> effect-var action-var (env/get-var s))
        _  (assert a)
        pm (:precond-map a)
        parent-map (env/get-vars s (map parent-var (keys (dissoc pm effect-var))))
        [set-parents unset-parents] (util/separate parent-map (keys parent-map))]
    (when (and (env/state-matches-map? s pm)
               (every? #(= (parent-map %) effect-var) set-parents)
               (every? #(nil? (env/get-var s (action-var (second %)))) unset-parents));; TODO: ugly
      (let [fire (make-fire-action-action a)]
        [(hierarchy/SimpleHLA [::GreedyFire ] (env/precondition-context fire s)
          [(conj (vec (for [p unset-parents] (make-set-parent-var-action (second p) effect-var))) fire)])
         (ActivateVarHLA hierarchy effect-var)]))))


(defn active-action-vars [hierarchy s]
  (filter #(env/get-var s (action-var %)) 
          (util/safe-get hierarchy :vars)))

(defn open-vars [hierarchy s]
  (remove #(or (env/get-var s (action-var %)) (env/get-var s (parent-var %))) 
          (util/safe-get hierarchy :vars)))

(defn supported-vars [hierarchy s]
  (mapcat (fn [v] (if-let [a (env/get-var s (action-var v))] 
                    (for [[var val] (:precond-map a)
                          :when (not (= (env/get-var s var) val))]
                      var)
                    (if-let [p (env/get-var s (parent-var v))] [p])))
          (util/safe-get hierarchy :vars)))


(deftype AddSomeActionHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::AddSomeAction effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s]
     (assert (not (or (env/get-var s (parent-var effect-var)) (env/get-var s (action-var effect-var)))))
     #{effect-var})
  hierarchy/HighLevelAction
   (immediate-refinements- [s] 
     (assert (not (or (env/get-var s (parent-var effect-var)) (env/get-var s (action-var effect-var)))))
     (for [[eval actions] (util/safe-get-in hierarchy [:dtgs effect-var (env/get-var s effect-var)])
           a actions]
       [(make-add-action-action a)]))
   (cycle-level-           [s] nil))


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
     ((util/safe-get hierarchy :parent-var-map) effect-var))))

;; TODO: should not add actinos if only current val can be needed.

(deftype ActivateVarHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::PostFire effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] 
    (set (cons effect-var 
               (apply concat 
                 (for [v ((util/safe-get hierarchy :parent-var-map) effect-var)]
                   [v (action-var v)])))))
  hierarchy/HighLevelAction
   (immediate-refinements- [s]
     (if (= effect-var sas/goal-var-name) [[]]
      (cons [(AddSomeActionHLA hierarchy effect-var)]
            (for [p (possible-parents hierarchy s effect-var)]
              [(make-set-parent-var-action effect-var p)]))))
   (cycle-level-           [s] nil))

; Note: ideally, when we add actions we care about support.  
 ; From below --> potentail for acyclic actions, only to desired val.
 ; From above --> also need support from below, in that
  ; can use current val of child *first* by action on this var, driven by bottom-up.
   ; (prunes action choice, can be recognized early to prune whole state.)

(defn choose-open-var 
  "Choose a var to start changing.  Var must be open, i.e. parent-var and action-var both nil.
   Var should be supported, either 
     -from below by open precondition of action on potential parent-var, or
     -from above by parent-var link to this var."
  [hierarchy s]
  (first (filter (set (supported-vars hierarchy s)) (open-vars hierarchy s))))

(deftype FlatASPlanHLA [hierarchy name pc] :as this
  env/Action
   (action-name [] name)
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [s] pc)
  hierarchy/HighLevelAction
   (immediate-refinements- [s] 
     (if-let [actives (seq (active-action-vars hierarchy s))]
       (if-let [greedy (some #(make-greedy-fire-plan hierarchy s %) actives)]
         [(conj (vec greedy) this)]
         (when-let [open (choose-open-var hierarchy s)]
;  Note; this can cause suboptimalify if someone might want current val.           
;          [[(AddSomeActionHLA hierarchy open) this]]))

           [[(ActivateVarHLA hierarchy open) this]]))
       [[]]))
   (cycle-level-           [s] nil))

(defn make-flat-asplan-hla [hierarchy full-context]
  (FlatASPlanHLA hierarchy [::FlatASPlan] full-context))



;; TODO: cutoff when top-down and bottom-up meet, don't match ? 

;; TODO: note, should be able to use acylic dtgs for, e.g., single parent. 

;; TODO: Take advantage of "greedy-chain" condition, don't assign
;   val to parent too high up the chain too early. 


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

(deftype ASPlanFlatHierarchy [sas-problem vars dtgs parent-var-map possible-next-map])

(defn make-asplan-flat-hierarchy [sas-problem dtgs] 
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        parent-var-map (util/map-vals #(map second %) (util/group-by first causal-graph))]
    (assert (graphs/dag? causal-graph))
    (ASPlanFlatHierarchy
     sas-problem 
     (keys (:vars sas-problem))
     dtgs
     parent-var-map
     (compute-possible-next-map dtgs))))

(defn make-asplan-env [sas-problem dtgs]
  (reify env/Env
   (initial-state [] 
     (expand-initial-state (env/initial-state sas-problem) (goal-action dtgs)))
   (actions-fn    [] :no-actions-fn)
   (goal-fn       [] (env/goal-fn sas-problem))))

(defn make-asplan-flat-henv [sas-problem] 
  (let [dtgs (sas-analysis/domain-transition-graphs sas-problem)
        env  (make-asplan-env sas-problem dtgs)]
    (hierarchy/SimpleHierarchicalEnv 
     env
     [(make-flat-asplan-hla (make-asplan-flat-hierarchy sas-problem dtgs) 
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

