(ns exp.asplan
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] ]
            [exp [env :as env]  [hierarchy :as hierarchy] 
                 [sas :as sas] [sas-analysis :as sas-analysis]]))



; TODO: define as HLA or not?  Can define

; Greedy: if all preconds met, ...
; Questions about what must go in HLA name. 

; Would like to avoid cycles, somehow ...

; Also should not include "buried" actions in name.

; How can we abstract?
 ; Goal at each point is to fire at least one of existing actions.  
   ; All actions that cannot fire first can be ignored, as can 
   ; values of locked non-precond vars, and irrelevant vars. 
 ; If set of such vars are disjoint across actions, decompose. 
; Problem with this: can decompose to "first then rest", but how does rest know which fired?
 ; Can just look at state?  This seems, mmm, awkward, but maybe OK.
   ; Except: we can also end up adding unfired actions ?
   ; Can certainly just ignore these commitments... but this can multiply states  
   ; Can try to require that all such actions fire 
     ; correct?
   ; Also, would like to assert that all actions were *relevant* to fired action.
   ; Problem: fire A, generate floating B, needed.
   ; Sol: put stuff into state ? 
 ; Alternative is to use generalized-goal search.

; For now, pretend analysis is free, just brute-force it. 

; OK, so we put stuff in state.  
; For each var, a second var pointing to: pending action, :frozen, or :open
;  This doesn't play with usual state abstraction.
;  Instead, can have var-in-use, var-action, latter always nil if not in-use.
;    This allows us to abstract away action if we want.  
;    Annoying: we now have to have primitives for changing this extra state. 
;  Except, we also need to keep track of *user* of frozen far w/o action.


;; Attempt at concrete outline:

; Start with only "goal" action active.  
; Do "fire any action" search.

; "Fire any action" search:
 ; If any action can fire greedily (with free or self-reserved preconds), fire, goal.
 ; Otherwise, pick an ("unblocked"?) action,
  ; and a free precond for that action
    ; and set var to "active".

; If a var is "active", either
 ; Add an action applicable iwth current value that changes it.
 ; "Freeze" it in service of some other var, which has this val as possible next.  

; Question: do we additionally need to keep token to guide refs?

; We have simple, dijkstra-shared-goal options, with same acylic options.

; Can refine until *particular* action resolved, or *any* current action resolved. 
;   (not just any action, steps are too small).

;; TODO: should we allow action to fire even when there is already action scheduled on precond ?



;; TODO: also look at using landmarks to structure search ? 

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Types, Protocols, Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype ASPlan-Hierarchy 
  [sas-problem])

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
; Doing so seems to require set-valued conditions, so skip it. 
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

(declare PostFireActionHLA)

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
         (PostFireActionHLA hierarchy effect-var)]))))


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

;; Also, Start actions on a var.  Assumption: doing it for a parent that wants a diff. val
; from this var. 
(deftype AddActionHLA [hierarchy effect-var]
  env/Action
   (action-name [] [::AddAction effect-var])
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

(deftype PostFireActionHLA [hierarchy effect-var]
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
      (cons [(AddActionHLA hierarchy effect-var)]
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
           [[(AddActionHLA hierarchy open) this]]))
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

(deftype ASPlanHierarchy [sas-problem vars dtgs parent-var-map possible-next-map])
(defn make-asplan-hierarchy [sas-problem dtgs] 
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        parent-var-map (util/map-vals #(map second %) (util/group-by first causal-graph))]
    (assert (graphs/dag? causal-graph))
    {:type              ::ASPlanHierarchy
     :sas-problem       sas-problem
     :vars              (keys (:vars sas-problem))
     :dtgs              dtgs
     :parent-var-map    parent-var-map 
     :possible-next-map (compute-possible-next-map dtgs)}))

(defn make-asplan-env [sas-problem dtgs]
  (reify env/Env
   (initial-state [] 
     (expand-initial-state (env/initial-state sas-problem) (goal-action dtgs)))
   (actions-fn    [] :no-actions-fn)
   (goal-fn       [] (env/goal-fn sas-problem))))

(defn make-asplan-henv [sas-problem] 
  (let [dtgs (sas-analysis/domain-transition-graphs sas-problem)
        env  (make-asplan-env sas-problem dtgs)]
    (hierarchy/SimpleHierarchicalEnv 
     env
     [(make-flat-asplan-hla (make-asplan-hierarchy sas-problem dtgs) 
                            (env/current-context (env/initial-state env)))])))

(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) (map env/action-name sol))))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])

; (let [e (make-random-infinite-taxi-sas2 1 2 1 2)] (println (run-counted #(uniform-cost-search e))) (println (run-counted #(asplan-solution-pair-name (debug 0 (sahucs-fast-flat (make-asplan-henv e )))))))

(comment 
)

; (-> (make-asplan-hierarchy (make-random-infinite-taxi-sas2 3 3 1 1)) :env initial-state)

(comment
  (declare var-free? var-val ...)



  (deftype ASPlanHLA [hierarchy name precond-var-set
                      pending-action-set frozen-var-set last-thing]
    :as this
    env/Action
    (action-name [] name)
    (primitive?  [] false)
    env/ContextualAction 
    (precondition-context [s] precond-var-set)
    hierarchy/HighLevelAction
    (immediate-refinements- [s] 
                            (let [cur-val (env/get-var s var)]
                              (if (= cur-val dst-val)
                                [[]]
                                (for [as (vals (get dtg cur-val)), action as]
                                  [(make-action-hla hierarchy action) this]))))
    (cycle-level-           [s] 
                            (when ((:cycle-to hierarchy) var dst-val)
                              ((:var-levels hierarchy) var)))))


(comment 
  (declare make-action-hla)




  (defprotocol SDH-HLA
    (active-var-set  [a])
    (leaf-var-set    [a])
    (needs-expand?   [a])
    (expand          [a lv])          ; returns [[action-seq new-hla]]
    (greedy-select?  [a s v av]) ; Has a descendent that can be done greedily.
    (select-leaf     [a s v av]) ; returns new-hlas. av is active-var set, lv is leaf-var set
    ) 




  (defprotocol SDH-Precond-HLA
    (active?    [a])
    (satisfied? [a s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Active Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ?Note, for bookkeeping to work properly we have to retain an active precond in an action even if we have also pushed it out front.

; first-action can be null, iff we're done.

;; Note: can get primitives 

  (defn rec-immediate-refinements [a s]
    (hierarchy/immediate-refinements- a s))

  (defn effect-val [a]
    (val (util/safe-singleton (:effect-map (if (env/primitive? a) a (:action a) )))))

  (declare make-active-precond-hla)

  (deftype SDH-Active-Precond-HLA  [hierarchy name first-action leaf-precond active-var-set leaf-var-set] :as this
    SDH-HLA
    (active-var-set  []  active-var-set)
    (leaf-var-set    []  leaf-var-set)
    (needs-expand?   []  (needs-expand? first-action))
    (expand          [lv] 
                     (for [[prefix new-fa] (expand first-action lv)]
                       [prefix (if new-fa (make-active-precond-hla hierarchy new-fa leaf-precond) leaf-precond)]))
    (greedy-select?  [s v av] (greedy-select? first-action s v av))
    (select-leaf      [s v av] 
                      (for [new-fa (select-leaf first-action s v av)] 
                        (make-active-precond-hla hierarchy new-fa leaf-precond)))
    SDH-Precond-HLA  
    (active?     []  true)
    (satisfied?  [s] false)    
    env/Action
    (action-name [] name)
    (primitive?  [] false)
                                        ; env/ContextualAction 
                                        ;   (precondition-context [s] (env/precondition-context leaf-precond s))   
    )

  (defn- make-active-precond-hla [hierarchy first-action leaf-precond]
    (SDH-Active-Precond-HLA hierarchy 
                            [:!P+ (env/action-name first-action) (env/action-name leaf-precond)]
                            first-action leaf-precond
                            (clojure.set/union (active-var-set first-action) (active-var-set leaf-precond))
                            (leaf-var-set first-action)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Leaf Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (declare advance-active-leaf-precond-hla)

  (deftype SDH-Active-Leaf-Precond-HLA  [name inactive-leaf cur-val] :as this
    SDH-HLA
    (active-var-set  []  (leaf-var-set inactive-leaf))
    (leaf-var-set    []  (active-var-set inactive-leaf))
    (needs-expand?   []  (not (satisfied? this :dummy)))
    (expand          [lv] 
                     (let [{:keys [hierarchy var dst-val dtg]} inactive-leaf]               
                                        ;        (println cur-val dst-val)
                       (cond (empty? (clojure.set/intersection lv ((:interfering-set hierarchy) var)))
                             [[[inactive-leaf] (advance-active-leaf-precond-hla this dst-val)]]
                             (= cur-val dst-val)
                             [[[]     this]]
                             :else  
                             (for [[nv as] (get dtg cur-val), 
                                   :let [np (advance-active-leaf-precond-hla this nv)]
                                   action as
                                   :let [ahla (make-action-hla hierarchy action)]]
                               (if (env/primitive? ahla)
                                 [[ahla] np]
                                 [[] (make-active-precond-hla hierarchy ahla np)])))))
    (greedy-select?  [s v av] false)
    (select-leaf     [s v av] (throw (UnsupportedOperationException.)))
    SDH-Precond-HLA 
    (active?     []  true)
    (satisfied?  [s] (= cur-val (:dst-val inactive-leaf)))    
    env/Action
    (action-name [] name)
    (primitive?  [] false))

  (defn- advance-active-leaf-precond-hla [prev new-val]
    (SDH-Active-Leaf-Precond-HLA (:name prev) (:inactive-leaf prev) new-val))

  (defn- make-active-leaf-precond-hla [inactive-leaf cur-val]
    (SDH-Active-Leaf-Precond-HLA (assoc (:name inactive-leaf) 0 :!P*) inactive-leaf cur-val))


  (deftype SDH-Inactive-Leaf-Precond-HLA  [hierarchy name var dst-val dtg precond-var-set] :as this
    SDH-HLA
    (active-var-set  []  #{})
    (leaf-var-set    []  #{var})
    (needs-expand?   []  false)
    (expand          [lv] (throw (UnsupportedOperationException.)))
    (greedy-select?  [s v av] false)
    (select-leaf     [s v av] (assert (= v var)) [(make-active-leaf-precond-hla this (env/get-var s v))])
    SDH-Precond-HLA 
    (active?     []  false)
    (satisfied?  [s] (= (env/get-var s var) dst-val))    
    env/Action
    (action-name [] name)
    (primitive?  [] false)
    env/ContextualAction 
    (precondition-context [s] precond-var-set)
    hierarchy/HighLevelAction
    (immediate-refinements- [s] 
                            (let [cur-val (env/get-var s var)]
                              (if (= cur-val dst-val)
                                [[]]
                                (for [as (vals (get dtg cur-val)), action as]
                                  [(make-action-hla hierarchy action) this]))))
    (cycle-level-           [s] 
                            (when ((:cycle-to hierarchy) var dst-val)
                              ((:var-levels hierarchy) var))))

  (defn- make-inactive-leaf-precond-hla [hierarchy var dst-val]
    (SDH-Inactive-Leaf-Precond-HLA hierarchy [:!P var dst-val] var dst-val 
                                   ((:dtg-to           hierarchy) var dst-val)
                                   ((:ancestor-var-set hierarchy) var)))

;; TODO: when can greedy sat arise?  After creation, other-sat, or finish


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: actions need to fire; immediately; after completion of a precondition; greedily; ...
;; TODO: fire more than one greedy action at once ...
; ;TODO: how do we keep track of preconditions moved up front ?


  (declare make-action-hla)

;; NOTE: precond always needs expand after selection, even though it won't say so if satisfied.
;; this override is handled below.

  (deftype SDH-Action-HLA [hierarchy name action precond-var-set precond-hlas expand-index] :as this
    SDH-HLA
    (active-var-set []  (apply clojure.set/union (map active-var-set precond-hlas)))
    (leaf-var-set   []  (apply clojure.set/union (map leaf-var-set precond-hlas)))
    (needs-expand?  []  expand-index)
    (expand         [lv]
                    (assert expand-index)
                    (for [[prefix new-precond] (expand (precond-hlas expand-index) lv)
                          :let [next-hlas (assoc precond-hlas expand-index new-precond)]]        
                      (do ; (println (map env/action-name next-hlas) (env/action-name new-precond))
                        (if (and (satisfied? new-precond :dummy) (every? #(and (active? %) (satisfied? % :dummy)) next-hlas))
                          [(conj prefix action) nil]
                          [prefix (SDH-Action-HLA. hierarchy [:!A* (env/action-name action) (map env/action-name next-hlas)] 
                                                   action precond-var-set next-hlas                              
                                                   (when (needs-expand? new-precond) expand-index))]))))
    (greedy-select? [s v av] 
                    (or (every? #(and (satisfied? % s) (or (active? %) (not (av (:var %))))) precond-hlas)
                        (some #(greedy-select? % s v av) (util/make-safe (seq (filter #(contains? (leaf-var-set %) v) precond-hlas))))))
    (select-leaf    [s v av]
                    (let [possible-vals  (filter #(contains? (leaf-var-set (precond-hlas %)) v) (range (count precond-hlas)))
                          [deep shallow] (util/separate (comp active? precond-hlas) possible-vals)
                          val-options    (or (and (:greedy-optimization? hierarchy) 
                                                  (when-first [x (filter #(greedy-select? (precond-hlas %) s v av) deep)] [x])) 
                                             (seq deep) 
                                             (seq shallow))]
                      (assert (seq val-options))
                      (assert (<= (count shallow) 1))
                      (doall (for [idx         val-options,
                                   next        (select-leaf (precond-hlas idx) s v av)
                                   :let [new-precond-hlas (assoc precond-hlas idx next)]]
                               (SDH-Action-HLA. hierarchy [:!A* (env/action-name action) (map env/action-name new-precond-hlas)]
                                                action precond-var-set new-precond-hlas idx)))))
    env/Action
    (action-name     [] name)
    (primitive?      [] false)
    env/ContextualAction 
    (precondition-context [s] precond-var-set)
    hierarchy/HighLevelAction
    (immediate-refinements- [s]
                            (let [var-leaves  (leaf-var-set this)]
                              (if (needs-expand? this) ; Prevent loop where new trivial-sat prec.
                                (let [nexts  (for [[prefix nxt] (expand this var-leaves)] (if nxt (conj prefix nxt) prefix))]
                                  (if-let [a (util/singleton (util/singleton nexts))]
                                    (hierarchy/immediate-refinements- a s)
                                    nexts))
                                (let [var-actives (active-var-set this)
                                      var-options (clojure.set/difference var-leaves var-actives)]
                                        ;           (println "selecting...")
                                  (if (empty? var-options)
                                    (println "Dead end!")
                                    (map vector (select-leaf this s (util/first-maximal-element (:var-levels hierarchy) var-options) var-actives)))))))
    (cycle-level-           [s] nil))

  (defn- make-action-hla [hierarchy action]
    (let [effect-var (key (util/safe-singleton (:effect-map action)))
          reduced-em (dissoc (:precond-map action) effect-var)]
      (if (empty? reduced-em)
        action
        (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action
                        ((:ancestor-var-set hierarchy) effect-var)
                        (vec (for [[pvar pval] reduced-em] (make-inactive-leaf-precond-hla hierarchy pvar pval))) nil))))

;; TODO: 

;; suppose we have A and B, share some ancestor;
;; C, an ancestor of A but not B.  
;    C shares ancestors with B --> must interleave (constrained)
;    C shares no ancestors with B --> may as well 

; i.e., two actions must be interleaved if 
; - Have ancestors in common
; - Neither an ancestor of the other.

; i.e., go in topological order, keep clusters:
 ; each has (1) set of vars, (2) union of ancestors, (3) intersection of ancestors.
 ; new var is added to set if not in set 3, ancestors intersect with set 2.
 ; else left alone?
 ; Can a new precond ever "bridge" two previously separate ones?  Yes.
 ; so just do it by connected components?  Then, how do we order?




; (run-counted #(sahucs-inverted (make-simple-dag-hierarchy (make-sas-problem-from-pddl (prln (write-infinite-taxi-strips2 (make-random-infinite-taxi-env 2 2 1 6)))))))

; (let [p (make-sas-problem-from-pddl (write-infinite-taxi-strips2 (make-random-infinite-taxi-env 3 3 3 0)))] (println (time (run-counted #(second (uniform-cost-search p))))) (println (time (run-counted #(second (sahucs-inverted (make-simple-dag-hierarchy p)))))))







  (comment
  
  

    (deftype SDH-Action-HLA [hierarchy name action effect-var precond-var-set]
      env/Action
      (action-name     [] name)
      (primitive?      [] false)
      env/ContextualAction 
      (precondition-context [s] precond-var-set)
      hierarchy/HighLevelAction
      (immediate-refinements- [s] 
                              [(concat 
                                (let [pc-map   (dissoc (:precond-map action) effect-var)
                                      topo-pcs (sort-by #(- ((:var-levels hierarchy) %)) (keys pc-map))
                                      as-fn    (:ancestor-var-set hierarchy)
                                      edges    (apply concat
                                                      (for [pc topo-pcs] [pc pc])
                                                      (for [[pc1 & more-pcs] (util/iterate-while next topo-pcs)
                                                            :let [as1 (as-fn pc1)]
                                                            pc2 more-pcs
                                                            :let [as2 (as-fn pc2)]]
                                                        (cond (contains? as1 pc2) [[pc1 pc2]]
                                                              (some as1 as2)      [[pc1 pc2] [pc2 pc1]]
                                                              :else               [])))
                                      batches  (vals (second (graphs/scc-graph (distinct edges))))]
                                        ;          (println "Batches" batches "for" name "from" topo-pcs edges)          
                                  (for [pc-batch batches]
                                    (if (> (count pc-batch) 1)
                                      (do (println "Interleaving preconditions " pc-batch "for" name)
                                          (make-interleaving-hla hierarchy (select-keys pc-map pc-batch)))
                                      (let [pc (util/safe-singleton pc-batch)]
                                        (make-precond-hla hierarchy pc (get pc-map pc))))))
                                [action])])
      (cycle-level-           [s] nil))

    (defn- make-action-hla [hierarchy action]
      (let [effect-var (key (util/safe-singleton (:effect-map action)))]
        (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action effect-var
                        ((:ancestor-var-set hierarchy) effect-var))))


    ))