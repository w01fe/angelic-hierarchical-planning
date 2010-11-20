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

(defn action-var [v]       [:action v])
(defn free-var [v]         [:free? v])
(defn parent-var [v child] [:parent? v child])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a parent (in which case it must eventually be used to fire an active action on
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
       [[(action-var sas/goal-var-name) goal-action]
        #_ [(free-var sas/goal-var-name) false]]))))

(def *add-count* (util/sref 0))

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
  (util/sref-set! *add-count* (inc (util/sref-get *add-count*)))
  (let [[evar eval] (util/safe-singleton (seq effect-map))]
    (env-util/make-factored-primitive
     [::AddAction name]
     {(action-var evar) nil, evar (precond-map evar), (free-var evar) false}
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
                   (for [v precond-vars] [(parent-var v effect-var) true])))
     (into effect-map 
           (concat [[(action-var effect-var) nil]]
                   (for [v precond-vars] [(free-var v)              true])
                   (for [v precond-vars] [(parent-var v effect-var) false])))
     0)))


; Try to make an action that greedily fires the action scheduled on effect-var,
; effectively representing a composition of set-parent and fire-action actions.
(defn make-greedy-fire-action [s effect-var]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> effect-var action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
    (when (and (state/state-matches-map? s precond-map)
               (every? #(state/get-var s (parent-var % effect-var)) unfree-pv))
        (assert (every? #(nil? (state/get-var s (action-var %))) precond-vars))
        (env-util/make-factored-primitive
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


(defn activation-actions  "Return a list of all activation actions for var v"
  [child-map v]
  (for [c (child-map v)]
    (make-set-parent-var-action v c)))

(defn deadlocked? [s child-map extra-edges]
  (let [parent-edges (concat extra-edges 
                       (for [[p cs] child-map, c cs :when (state/get-var s (parent-var p c))] [p c]))
        res-map      (into {} (filter (fn [[p c]] 
                                        (when-let [a (state/get-var s (action-var c))]
                                          (contains? (:precond-map a) p))) 
                                      parent-edges))
        extra-edges  (for [[p c] parent-edges 
                           :let [a (state/get-var s (action-var p))] 
                           :when a
                           precond (remove #{p} (keys (:precond-map a)))
                           :let [res (res-map precond)]
                           :when res]
                       [res p])]
    (not (graphs/dag? (concat parent-edges extra-edges)))))

(comment
  ;; Not used for now?
  (defn var-not-usable? [s ancestor-map target-var a-var]
   (if-let [a  (state/get-var s (action-var a-var))]
     (let [pm (:precond-map a)]
       (every?
        (fn [pv] (or (= (state/get-var s pv) (pm pv)) (var-not-usable? s ancestor-map target-var pv)))
        (remove #{a-var} (keys pm))))
     (not (contains? (ancestor-map a-var) target-var)))))

;; TODO: dynamic bottom-up pruning.
 ; i.e., exists precondition of some current action, NOT currently achieved,
 ; that has every child of a parent-link in its ancestor-set. 
; Or, more simply, variables should "die off".  
;; TODO: generalize.  This is just special case for most logistics,
(defn dead-end? [s ancestor-map child-map extra-edges]
  (let [gpm      (:precond-map (state/get-var s (action-var sas/goal-var-name)))
        live-set (apply clojure.set/union #{sas/goal-var-name}
                        (for [pv (remove #{sas/goal-var-name} (keys gpm))
                              :when (not (= (state/get-var s pv) (gpm pv)))]
                          (ancestor-map pv)))]
    (some #(not (live-set (second %)))
          (concat extra-edges
            (for [[p cs] child-map, c cs :when (state/get-var s (parent-var p c))] [p c])))))

(defn possible-activation-actions  
   "Return a list of possible activation actions for var v possible in state s.
   To be possible parent, must be supported from below, and not cause deadlock
   (by pointing to action whose other precondition is needing it. "
   [s ancestor-map child-map v]
;   (activation-actions child-map v) #_
   
 (for [c (child-map v) :when (not (or (deadlocked? s child-map [[v c]])
                                      (dead-end? s ancestor-map child-map [[ v c]])))]
   (make-set-parent-var-action v c)))


(defn current-child [s child-var-map p-var]
  (when-not (state/get-var s (free-var p-var))
    (util/find-first #(state/get-var s (parent-var p-var %))
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

(defrecord ASPlanEnv [init actions actions-fn g-map 
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
        av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
        child-var-map (util/map-vals #(map second %) (group-by first causal-graph))
;        vars          (keys (:vars sas-problem))
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (assert (graphs/dag? causal-graph))    
;    (clojure.inspector/inspect-tree child-var-map)
    (ASPlanEnv. 
     (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
     (concat
      (for [a (:actions sas-problem)] (make-add-action-action a))
      (for [[p cs] child-var-map, c cs] (make-set-parent-var-action p c))
      (for [a (:actions sas-problem)] (make-fire-action a)))
     (fn asplan-actions [s]
;      (if false ;(deadlocked? s child-var-map)
;        (do (println s) nil)
      (when-not (dead-end? s av-map child-var-map []);)
       (let [[aa-vars na-vars] (util/separate #(state/get-var s (action-var %)) vars)
             aa-parent-edges   (for [av aa-vars
                                      :let [pm (:precond-map (state/get-var s (action-var av)))]
                                      pv    (remove #{av} (keys pm))
                                      :when (and (not (state/get-var s (action-var pv)))
                                                 (not (= (pm pv) (state/get-var s pv))))]
                                  [pv av])
             na-tuples         (for [nav na-vars
                                     :let  [child (current-child s child-var-map nav)]
                                     :when (and child (not (state/get-var s (action-var child))))]
                                 [nav child])]
;         (println "\n\n\n" s "\n\n" (:act-seq (meta s)) "\n")
;         (println "\n\n\n" s "\n"  aa-vars "\n"  aa-parent-edges "\n" na-tuples )
;        (util/prln
         (util/cond-let [x]
          ;; Greedy action -- all preconditions satisfied and not assigned elsewhere
          (some #(make-greedy-fire-action s %) aa-vars) 
            [x]

          ;; Active bottom-up var -- assigned, needs its value changed.               
          (util/find-first (fn [[pv cv]] (state/get-var s (parent-var pv cv))) aa-parent-edges)
            (let [[pv cv] x, 
                  p-val (state/get-var s pv)
                  d-val ((:precond-map (state/get-var s (action-var cv))) pv)
                  dtg   (get-in dtgs [pv p-val])]
              (for [n-val (acyclic-succ-fn pv p-val d-val), a (dtg n-val)]
                (make-add-action-action a)))

          ;; Inactive bottom-up var -- needs to be assigned.  
          (util/find-first #(state/get-var s (free-var %)) (map first aa-parent-edges))
            (possible-activation-actions s av-map child-var-map x)

          ;; Active top-down var -- add actions
          (util/find-first #(not (state/get-var s (free-var %))) (map second na-tuples))  
            (do (println "A!" x (state/get-var s x) (state/get-var s (parent-var x sas/goal-var-name)))
             (for [as (vals (util/safe-get-in dtgs [x (state/get-var s x)])), a as]
               (make-add-action-action a)))

          ;; Inactive top-down var -- activate it
          (util/find-first #(state/get-var s (free-var %)) (map second na-tuples))
            (do (println "I!")
             (possible-activation-actions s av-map child-var-map x))
            
            ))) )
     (env/goal-map sas-problem)
     causal-graph dtgs av-map child-var-map acyclic-succ-fn)))

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
     [goal-var goal-val]]))


;; TODO: cutoff when top-down and bottom-up meet, don't match ? (or earlier)

;; TODO: Take advantage of "greedy-chain" condition, don't assign



;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'edu.berkeley.ai.util 'angelic.sas.hm-heuristic)

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


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

; Then, only question is recovery?  Only end up with actions already present if we 
; deadlocked before?  Can just walk back up, it's fine ... but hopefully can detect
; whether deadlock possibly avoided before doing lots of work. 

; One idea: can record "deadlock roots".  i.e., each set parent-var can deadlock a whole subtree.  
; this should really be metadata.  

; Note: what happened to possible-next sets above?  Can use them to filter outside parent-var commitments, once we get up to level where context is apparent.

; Note: in general may be able to improve on precondition context, by taking top-down
;   info into account. ??


;; OK, (almost) enough talk.  
; HLAs will be:
; FireAction -- fires action or deadlocks trying -- not cyclic
 ; If greedy action possible, refine to that
 ; If deadlocked, refine to empty plan
 ; Else, if active precondition with wrong val (non-DL), try to achieve + recursive
 ; Else, if inactive precondition with wrong val, activate + recursive
 ; Else, pick a top-down opportunity in scope, and advance that
    ; Can just fall back to "primitive" actions fn ?!?!
 ; Basically, this is just primitive thing, with 2 differences: 
  ; Only look locally at this action, except for top-down things. 
  ; Preconditions are achieved in one go using AchievePrecondition

; AchievePrecondition -- achieves precondition or deadlocks trying -- ideally aclycic, in practice?
 ; If correct value, empty sequence
 ; If active action, try to fire it + PostFireAttempt
 ; If no active action, add one (that can lead in right dir'n).

; PostFireAttempt:
 ; If action actually fired, AchievePrecondition; else, empty seq.

; Only question: how do we detect deadlocked precond in FireAction?
; For now, we can punt and use same solution as AchievePrecondition -- 
; keep deadlock set in FireAction, clear every time we come in, and rely on SA to save us.

; (ideally, SA just follows deadlock chain)

; Even better: keep track of deadlock var sets for each var
; (to fire current action on var, must free or ?? parent-links from ALL vars in set).
; Note: recursive scheme means will be *maximally deadlocked* when we come down.
;  e.g., every precondition will either be achieved (reserved or not), or deadlocked

;; For now, just do simplest thing, PostFireAttempt and PostAchieveAttempt

;; TODO: think about adaptive contexts.  

;; TODO: speed up somehow?

(declare precond-deadlocked?)
(defn action-deadlocked? [s var]
  (when-let [a (state/get-var s (action-var var))]
    (some #(precond-deadlocked? s % var) (remove #{var} (keys (:precond-map a))))))

(defn precond-deadlocked? [s precond e-var]
  (or (and (not (state/get-var s (free-var precond)))
           (not (state/get-var s (parent-var precond e-var))))
      (action-deadlocked? s precond)))

(defn precond-deadlocked-ooc? [s precond e-var child-var-map context]
  (or (and (not (state/get-var s (free-var precond)))
           (not (state/get-var s (parent-var precond e-var)))
           (not (contains? context (current-child s child-var-map precond))))
      (when-let [a (state/get-var s (action-var precond))]
        (some #(precond-deadlocked-ooc? s % precond child-var-map context) 
              (remove #{precond} (keys (:precond-map a)))))))




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
                     (assert (not (state/get-var s av))) [[]])
               (state/get-var s av)
                 (if (action-deadlocked? s var) 
                     (do ;(print "!D") 
                       [[]])
                   (do ;(print "!A") 
                       [[(make-fire-action-hla hierarchy var (state/get-var s av)) this]]))
               :else 
                 (let [p-val (state/get-var s var)
                       dtg   (util/safe-get-in hierarchy [:dtgs var p-val])]
                   ;(print "!C")
                   (for [n-val ((:acyclic-succ-fn hierarchy) var p-val dst-val), a (dtg n-val)]
                     [(make-add-action-action a) this]))))
       (cycle-level-           [a s] nil))))




;(let [e (make-random-infinite-taxi-sas2 5 5 5 1) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))   (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))

;; TODO: A/I support is incorrect for now, it seems. 
; OK, this is screwy for now, it seems.
; We need to be able to transfer control to floating actions? 

(defn make-fire-action-hla  [hierarchy effect-var a]
  (let [name          [:fire-action effect-var]
        reduced-pm    (dissoc (:precond-map a) effect-var)
        ancestor-vars (util/safe-get-in hierarchy [:ancestor-var-map effect-var])
        child-var-map (:child-var-map hierarchy)
        context-cvm   (util/map-vals
                       #(filter ancestor-vars  %)
                       (select-keys child-var-map ancestor-vars))
        pc (into #{(action-var effect-var)}
                 (apply concat
                        (for [v (distinct (apply concat (for [p (keys reduced-pm)] (util/safe-get-in hierarchy [:ancestor-var-map p]))))]
                          (concat 
                           [v (free-var v) (action-var v)]
                           (for [c (child-var-map v) :when (ancestor-vars c)] (parent-var v c))))))
        

           #_(into #{(action-var effect-var)}
                            (apply concat
                                   (for [p (keys reduced-pm)]
                                     (cons (parent-var p effect-var)
                                           (util/safe-get-in hierarchy [:precondition-context-map p])))))
        ;                                   (map (:fire-action-pc-map hierarchy) (keys reduced-pm))
;        pc (:full-context hierarchy)
        ]
;    (println "FA" name pc "\n" (clojure.set/difference (:full-context hierarchy) pc))
  (reify
    env/Action
      (action-name [a] name)
      (primitive?  [a] false)
    env/ContextualAction 
      (precondition-context [a s] pc) ;; perhaps can do better?
    hierarchy/HighLevelAction
      (immediate-refinements- [this s] 
;        (Thread/sleep 10)
        (assert (= (state/get-var s (action-var effect-var)) a))
        (let [na-tuples         (for [nav   ancestor-vars
                                      :when (not #(state/get-var s (action-var %)))
                                      :let  [child (current-child s child-var-map nav)]
                                      :when (and child (ancestor-vars child) (not (state/get-var s (action-var child))))]
                                  [nav child])]
         (util/cond-let [x]
          ;; Greedy -- all preconditions satisfied and not assigned elsewhere
          (make-greedy-fire-action s effect-var)
            (do ;(print "g") (flush) 
              [[x]])

          ;; Real deadlock - fail (for SA, must restrict context...)
          (deadlocked? s context-cvm []) 
            (do ;(print "d") (flush)
               nil)
            
          ;; Deadlocked by something out-of-context -- exit  (note -- need to check for goal means
            ; we should catch these issues earlier..
          (some #(precond-deadlocked-ooc? s % effect-var child-var-map ancestor-vars) (keys reduced-pm))
            (do ;(print "x") (flush)
                (when-not (= effect-var sas/goal-var-name) [[]]))

          ;; Active precondition -- assigned, needs its value changed, not deadlock               
          ;; TODO: order
          (util/find-first #(and (state/get-var s (parent-var % effect-var))
                                 (not (= (state/get-var s %) (reduced-pm %)))
                                 (not (precond-deadlocked? s % effect-var)))
                           (keys reduced-pm))
            (do ;(print "a" (if (state/get-var s (action-var x)) "o" "n")) (flush)
             [[(make-achieve-precondition-hla hierarchy x (reduced-pm x)) this]])

          ;; Inactive precondition -- needs to be assigned.  
          (util/find-first #(and (state/get-var s (free-var %))
                                 (not (= (state/get-var s %) (reduced-pm %))))
                           (keys reduced-pm))
            (do ;(print "i") (flush) 
             (for [a (activation-actions child-var-map x)]
               [a this]))

          ;; Active top-down var -- add actions
          (util/find-first #(not (state/get-var s (free-var %))) (map second na-tuples))  
            (do (println "A!");(print "a") (flush)
             (for [as (vals (util/safe-get-in (:dtgs hierarchy) [x (state/get-var s x)])), a as]
               [(make-add-action-action a) this]))

          ;; Inactive top-down var -- activate it
          (first (map second na-tuples))
            (do (println "I!"); (flush)
             (for [a (activation-actions child-var-map x)]
               [a this]))
            
          ;; Nothing to do here -- return upwards, or fail if goal-var
          :else
            (do ;(print "f") (flush)
              (when (and (= effect-var sas/goal-var-name) (not (deadlocked? s child-var-map  nil)))
                (def *bs* s))
              (when-not (= effect-var sas/goal-var-name) [[]])))))
       (cycle-level-           [a s] nil))))

(comment ; old, broken PC
  (for [p (keys reduced-pm)]
                             (cons (free-var p) 
                                   (cons (parent-var p effect-var) 
                                         (util/safe-get-in hierarchy [:fire-action-pc-map p])))))
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
        :ancestor-var-map         av-map
        :acyclic-succ-fn          (:acyclic-succ-fn env)
        :precondition-context-map pc-map
        :fire-action-pc-map       fa-map}
       sas/goal-var-name
       (state/get-var (env/initial-state env) (action-var sas/goal-var-name)))])))


(defn asplan-skip-solution-name [sol]
  (map second (filter #(= (first %) ::GreedyFire) (map env/action-name sol))))

(defn asplan-skip-solution-pair-name [[sol rew]]
  [(asplan-skip-solution-name sol) rew])



;; TODO: faster & early deadlock detection.
;; TODO: detect "out-of-context" deadlock, fail immediately.
;; TODO: precond ordering when we activate (handled by activation-actions?)

;; (use 'angelic.search.explicit.hierarchical)

;; TODO: (let [e (make-random-infinite-taxi-sas2 3 2 5 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e)))))))) gives bad results; replacing inverted iwht regular fixes it ... ?

;; minimal exmaple:
;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 1 2 i)] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e)))))))))

;  (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))

; (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (interactive-hierarchical-search (make-asplan-skip-henv e)))

; (let [e (make-random-infinite-taxi-sas2 2 2 2 2)] (interactive-hierarchical-search (make-asplan-skip-henv e)))

; (let [e (force (nth ipc2-logistics 0))] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e))))))  (println (debug 0 (time (run-counted #(asplan-skip-solution-pair-name (dsh-ucs-inverted (make-asplan-skip-henv e))))))))






(comment
 (defn make-if-deadlock-hla [hierarchy var dl-plan nodl-plan]
   (let [name [:if-deadlock var (map env/action-name dl-plan) (map env/action-name nodl-plan)]
         av   (action-var var)
         pc   (util/safe-get-in hierarchy [:precondition-context-map var])]
     (reify :as this
            env/Action
            (action-name [_] name)
            (primitive?  [] false)
            env/ContextualAction 
            (precondition-context [_ s] pc)
            hierarchy/HighLevelAction
            (immediate-refinements- [_ s] (if (state/get-var s av) [dl-plan] [nodl-plan]))
            (cycle-level-           [s] nil)))))






















(comment ; May use later for more fine-grained stuff.
 (defn split-preconds 
   "Return [deadlocked matching free-unmatching reserved-unmatching]"
   [s effect-var reduced-pm deadlock-set]
   (let [[blocked unblocked] (util/separate #(or (deadlock-set %)
                                                 (and (not (state/get-var s (free-var %)))
                                                      (not (state/get-var s (parent-var % effect-var)))))
                                            (keys reduced-pm))
         [matching no-match] (util/separate #(= (reduced-pm %) (state/get-var s %)) unblocked)
         [free reserved]     (util/separate #(state/get-var s (free-var %))) no-match]
     [blocked matching free reserved])))







; AddActions, then set-parent-var.   
; Can return either a state where precondition accomplished, or 
; there exist a chain of actions (posisbly empy) leading to a precondition assigned
; outside the context of this precond.  
(comment
(defn make-fire-action-hla [hierarchy var action]
  (assert (= var (key (util/safe-singleton (:effect-map action)))))
  (let [name [:fire var]
        pc   (util/safe-get-in hierarchy [:precond-sets var])
        pm   (dissoc (util/safe-get action :precond-map) var)]
    (reify :as this
      env/Action
       (action-name [_] name)
       (primitive?  [] false)
      env/ContextualAction 
       (precondition-context [_ s] pc)
      hierarchy/HighLevelAction
       (immediate-refinements- [_ s]
         (assert (= (state/get-var s (action-var var)) action))
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


; ALSO: where does better deadlock detection come in ? 

)




(comment ; Version that does not care about target or parent ..
(deftype AddSomeActionHLA [hierarchy effect-var]
  env/Action
   (action-name [_] [::AddSomeAction effect-var])
   (primitive?  [] false)
  env/ContextualAction 
   (precondition-context [_ s] #{effect-var})
  hierarchy/HighLevelAction
   (immediate-refinements- [_ s] 
     (assert (not (state/get-var s (free-var effect-var))))
     (assert (not (state/get-var s (action-var effect-var))))
     (for [[eval actions] (util/safe-get-in hierarchy [:dtgs effect-var (state/get-var s effect-var)])
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
   (let [eval (state/get-var s effect-var)]
     (filter
      (fn [p]
        (if-let [pa (state/get-var s (action-var p))]
          (condp = (get (:precond-map pa) effect-var)
            nil  (can-use-next? hierarchy effect-var eval p (get (:effect-map pa) p))
            eval true
            false)
          (can-use-next? hierarchy effect-var eval p (state/get-var s p))))
      ((util/safe-get hierarchy :child-var-map) effect-var)))))




(comment ;; Not actually needed -- use below instead.
  (defn make-fire-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive}]
   (let [[evar eval] (util/safe-singleton (seq effect-map))]
     (env-util/make-factored-primitive
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