(ns angelic.search.action-set.gasplan2
  (:require [angelic.util :as util]
            [angelic.util.graphs :as graphs]
            [angelic.util.queues :as queues]            
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis]
            clojure.inspector)
  (:import [java.util HashMap]))


;; Generalized version of asplan for non-unary domains forked from,
;; gasplan, with partial commitment features of asplan2, effect
;; clusters of asplan_c, implicitly resource features of asplan_r.

;; no greedy for side-effects,
;; no directed unless all side effects scheduled,

;; Need to identify possible actions, children given commitments.
;; I.e., for resources no actions should e allowed, that propagates.



;; Current handling of greedy can be exponential when there are multiple
;; actions with same effects that can greedily fire.  or even not
;; Note greedy is not as pretty in this context, since we've got
;; more possible sets.  i.e., greedy is not a singleton.
;; This means that generalized goal thing doesn't actually work?
;; (since set encodes where we've been).  States need to be grouped.
;;  (and this is what the separate search does).
;; Is there a way around this? Suppose we just don't remove greedy fire from the set.
;; Then we wander around until we run out of steam -- just as desired.
;;  Only problem is if there are multiple precondition vars --
;; then we become incomplete.  Freezing is how we usually avoid this.
;; Think this should work, but in any case there will be tradeoffs.  Skip it for now.

;; In general, need to think about what to do with greedy.
;; Basic idea: for all children, look for greedy actions to fire.  This would be
;; faster but not simpler or asymptotically better.  Just skip it for now.

;; Can VPG stuff handle action disjunction ? Or identify greedy ?
;; Tricky.  Seems at minimum we have to commit to action schema up front.
;; Maybe.  Maybe not, greedy can be identified separately.
;; VPG is mostly to find deadlocks.

;; Just do something for now.

;; Simplify into just "bottom-up", "top-down", or "fire".
;; Can wait until all are ready to fire to fire.
;; May not happen, may have greedy ones with different schemas.
;; Can split them out when we pick a var.  Or wait until all ready.
;; let all ready be priority case ?
;; top-down case == reserved for wait.  Parent either frozen or wait.
;; Just skip town-down case initially?

;; Last question, how to handle blind side effects
;; Skip it for now.


;; MAYBE: do all the splitting and choosing at once?


;; TODO: if there are side-effecting actions, might not want to choose a value just yet,
;;       since we're not really goal directed anyway. -- except, fired actions encodes path?

;; NOTE: directed doesn't work, e.g., for package in transport because of side effects...
;;       this is as it should be -- suppose cap-1 truck.  May need to put down & re-pick.


;; How auxilary works:
;; Clearly, should prefer to pick canonical var child first,
;;   and this should determine the child of auxiliary vars.
;; This happens when listing possible children,
;;   and when finding parents (consider as part of block edge).
;; If we're greedily OK with canonical, not clear what to do. -- TODO: figure out



;;;;;;;;;;;;;;;;;;;;; Misc TODOs 
;; TODO: add clusters -- leave out for now.
;; TODO: add top-down, leave out for now.
;; TODO: identify superflous resources -- i.e., over-capacity trucks.
;; TODO: better heuristics
;; TODO: generalized goal ?
;; TODO greedy for 'nice' side-effects (doesn't really matter?)
;; TODO: Will still have to handle dangling effects.
;; TODO: have to see if multiplying will kill us.
;; TODO: prevail tsi is missing some vars
;; TODO: use other forward simplification ?

;;;;;;;;;;;;;;;;;;;;; Partition ordering
;; ** TODO: only work on preconditions of blocked actions if they can resolve
;;       blocking of blocker
;; TODO: consider depth-first ordering instead.  Tension between greedy and intention space size.


;;;;;;;;;;;;;;;;;;;;; Child pruning
;; TODO: don't choose dead var as child?
;;       further: don't choose as child if current action will kill (i.e., final drop).
;; TODO: prune children based on which values can actually be used next.  I.e., gripper in blocks world.
;;       if all next actions require a variable p, plus
;;       a different value on some other variable s.t. acheiving requires p,
;;       this variable cannot be next child of p.
;; TODO: additional child pruning.  If action has multiple prevails:
;;    if p reserved for v with action a, a also needs u,
;;    when selecting child for u, skip children where all
;;    next actions that need u also need v.
;;    Can be implemented with implied edges in VPG.
;;     (this generalizes auxiliary notion?)
;; LATER TODO: if children need same value, don't need to choose ?

;; Implied edges: if var has reservation for u
;; 

;;;;;;;;;;;;;;;;;;;;; Auxiliary 
;; TODO: don't allow reserving truck for capacity (??)
;;       note: careful, since if t1 on p1, p1 wants t2 first,
;;             prevail rules don't allow making tc1 parent of p1.
;; TODO: should not even allow actions on capacity ?
;;       (sometimes need it, i.e., gas-up only at gas stations).


;;;;;;;;;;;;;;;;;;;;; Action pruning
;; LATER TODO: object symmetries?
;;       if parents are symmetric, don't need to choose between them...
;; Done: conflicting preconditions, effects.



;; Suppose t1 reserved for p1, p1 wants t2 next.
;; If we try to reserve capacity for p2, we fail.
;; Notes: we actually should allow reserve capacity for p2,
;;        since we could generate action for p1-t1 from p2?  Nope, can't.
;; Case is covered by reserving t1 for tc1?  Seems OK.


;;;;;;;;;; Implementation notes

;; Pesky side effects (without preconds)...
;; Can try to deal with them head-on, or remove them from domain.
;; To remove them in most cases, can do analysis to find entailment
;; relationships of the form: if v=x, then u=y, use these to fill in
;; missing preconditions.
;; To deal with them head-on, we can reserve 


;;;;;;;;;;;;;;;; Auxiliary

;; How can we get around auxiliary reservation problem in nice way?
;;  Can say, no reservy unless you own canonical.
;;  This means you must be able to reserve canonical even if want value greedily.
;;  If you don't own canonical, we don't generate the edge.

;; Actions on auxiliary not needed since when we generate them,
;;  it must be reserved for a var 
;; And auxiliary as child of canonical should be prevented by child pruning, based on this fact.

;; TODO/  note: if multiple auxiliaries for single canonical, don't necessarily want to
;;         choose for canonical -- screws up greedy. 

;; Note: if t1 reserved for tc1, and p1 wants t1, p1 is blocked on tc1, also wants tc1.
;;       this is not quite a deadlock.  Top-down could resolve this.
;;       Failure is in 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

;; set of actions or :wait if not active.  Empty if frozen
(defn possible-actions-var [v] [:actions v]) 
;; assigned child (set) or nil if not reserved.
(defn child-var            [v] [:child v])  


(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a child (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init vars goal-action]
  (state/set-vars init
    (concat 
     (for [v vars] [(possible-actions-var v) :wait])
     (for [v vars] [(child-var v) nil])
     [[(possible-actions-var sas/goal-var-name) #{goal-action}]])))

(defn target-value [s v]
;  (println "\n" s v)
  (if (= v sas/goal-var-name)
    sas/goal-true-val
    (let [c (state/get-var s (child-var v))]
      (assert c)
      (util/safe-get (:precond-map (first (state/get-var s (possible-actions-var c)))) v))))



(defn make-set-actions-action [v actions]
  (assert (set? actions))
  (env-util/make-factored-primitive
   [::SetActions v actions]
   {}
   {(possible-actions-var v) actions}
   0))

(defn make-set-child-action [p c]
  (env-util/make-factored-primitive
   [::SetChild p c]
   {}
   {(child-var p) c}
   0))


;; TODO: possible actions should know about other commitments, etc.
(defn make-bottom-up-expand-action [s p c wanting-actions next-actions]
  (assert (or (= :wait wanting-actions) (set? wanting-actions)))
  (assert (or (= :wait next-actions) (set? next-actions)))
  (assert (= :wait (state/get-var s (possible-actions-var p))))
  (when-let [old-child (state/get-var s (child-var p))] (assert (= old-child c)))
  (env-util/make-factored-primitive
   [::Commit p c wanting-actions next-actions]
   {}
   {(child-var p) c
    (possible-actions-var c) wanting-actions
    (possible-actions-var p) next-actions}
   0))


(defn child-unavailable "Return blocking child, or nil" [s p c]
  (when-let [cur-c (state/get-var s (child-var p))]
    (when-not (= cur-c c) cur-c)))

(defn can-greedily-use? [s a p-var e-var]
  (util/assert-is (not (child-unavailable s p-var e-var)) "%s" [s a p-var e-var])
  (and (= (util/safe-get (:precond-map a) p-var) (state/get-var s p-var))
       (let [pav (state/get-var s (possible-actions-var p-var))]
         (or (and (= pav :wait) (not (contains? (:effect-map a) p-var)))
             (= pav #{})))))

;; TODO: free increases.
(defn make-greedy-fire-action [s a effect-var next-actions]
  (doseq [pvar (keys (dissoc (:precond-map a) effect-var))]
    (util/assert-is (can-greedily-use? s a pvar effect-var))
    (assert (contains? #{#{} :wait} (state/get-var s (possible-actions-var pvar)))))
  (assert (contains? (state/get-var s (possible-actions-var effect-var)) a))  
  (env-util/make-factored-primitive
   [::Fire a next-actions]
   {}
   (into (:effect-map a)
         (apply concat
           [[(possible-actions-var effect-var) next-actions]]           
           (for [[pvar pval] (dissoc (:precond-map a) effect-var)]
             [[(child-var pvar) nil]
              [(possible-actions-var pvar) :wait]])))
   (:reward a)))


(defn make-teleport-action [var from-val to-val rew]
  (env-util/make-factored-primitive
     [::Teleport var from-val to-val]
     {var from-val}
     {var to-val}
     rew))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitive Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers - Action Generation ;;;;;;;;;;;;;;;;;;;;;;;;;

(defn backward-reachable-nodes-and-preds [^HashMap cache simple-dtgs var-name to-val]
  (util/cache-with cache [:backward var-name to-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (map reverse (util/safe-get simple-dtgs var-name)) to-val)))

(defn possibly-acyclic-successors
  "Return a list of successors of cur-val, which can potentially lead to dst-val
   without a cycle."  
  [cache simple-dtgs var cur-val dst-val]
  (when-not (= cur-val dst-val)
   (let [backward-sets (backward-reachable-nodes-and-preds cache simple-dtgs var dst-val)]
     (for [[s t] (util/safe-get simple-dtgs var)
           :when (and (= s cur-val) (not (contains? (backward-sets t) s)))]
       t))))

(defn reachability-map [dtg from-val]
  (let [q (queues/make-graph-search-pq)]
    (queues/pq-add! q from-val 0)
    (while (not (queues/pq-empty? q))
      (let [[v c] (queues/pq-remove-min-with-cost! q)]
        (doseq [[nv actions] (get dtg v)]
          (queues/pq-add! q nv (- c (apply max (map :reward actions)))))))

    (assert (:map q))
    (util/map-vals - (into {} (:map q)))))

(defn make-shortest-path-fn [dtgs]
  (let [h (HashMap.)]
    (fn [var from-val to-val]
      (get (util/cache-with h [var from-val] (reachability-map (dtgs var) from-val)) to-val))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers - VPG ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;





;; Miss out on pruning out subsets of blocked actions...


(defn group-by-keys [f s]
  (util/map-vals (partial map second) (group-by first (for [x s, k (f x)] [k x]))))

;; NOTE: could be much more efficient...
;; TODO: possible block?
;; TODO: when part? is true, this can be much more efficient?
(defn vpg-edge-map [s vars]
  (util/for-map [v vars]
   v
   (let [actions (state/get-var s (possible-actions-var v))]
     (case actions 
       :wait nil
       #{} (when-let [c (state/get-var s (child-var v))] [[:frozen c]])
       (remove nil?
        (for [[p-var p-actions] (dissoc (group-by-keys (comp keys :precond-map) actions) v)]
          (if-let [block (child-unavailable s p-var v)]
            (when (= (count p-actions) (count actions)) [:block block])
            (let [need-count (util/count-when #(not (can-greedily-use? s % p-var v)) p-actions)]
              (cond (= need-count (count actions)) [:necessary-precond p-var]
                    (> need-count 0)               [:possible-precond p-var])))))))))

(defn vpg-edges [vpg exclude-set]
  (for [[out-var edges] vpg
        [edge-type in-var] edges
        :when (not (exclude-set edge-type))]
    [in-var out-var]))


(defn source-vars
  "Take the graph from var-ordering-edges, and return the sources in the same component
   as the goal variable, which are ripe for action.  Returns nil if there are any cycles
   in the graph, since this indicates a deadlock (at least some actions cannot fire)."
  [edges check-components?]
  (let [sources (clojure.set/difference (set (cons sas/goal-var-name (map first edges))) (set (map second edges)))
        goal-component-sources
        (if check-components?
          (clojure.set/intersection
           sources
           (graphs/ancestor-set (cons [sas/goal-var-name sas/goal-var-name] edges) [sas/goal-var-name]))
          sources)]
    (when-not (= (count sources) (count goal-component-sources)) (println "Warning: multiple components..."))
    goal-component-sources))


;; Tricky bit is that bottom-up can either give precondition or effect as source,
;; depending on if all actions want it or not.
;; Easier to split things up here, etc. 
(defn source-vars-by-type
  "Return a map from
    :greedy -> var with only greedy actions left on it
    :bottom-up -> map from precond vars to effect vars with at least one action needing res.
    :top-down -> whatever else"
  [s vars check-deadlock? check-components?]
  (let [edge-map (vpg-edge-map s vars)]
;    (println edge-map)
    (when (or (not check-deadlock?) (graphs/dag? (vpg-edges edge-map #{:possible-precond})))
      (let [precond-use-map (graphs/edge-list->outgoing-map (vpg-edges edge-map #{:frozen :block}))
            sources (source-vars (vpg-edges edge-map #{}) check-components?)
            [greedy other]  (util/separate #(let [as (state/get-var s (possible-actions-var %))]
                                              (and (not (= :wait as)) (seq as)))
                                           sources)
            [bottom-up bad] (util/separate #(and (= :wait (state/get-var s (possible-actions-var %)))
                                                 (seq (precond-use-map %)))
                                           other)]
;        (println greedy precond-use-map bottom-up bad)
        (when check-deadlock? (assert (seq sources)))1
        {:greedy greedy :bottom-up (select-keys precond-use-map bottom-up) :other bad}))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers - Pruning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: dynamic bottom-up pruning.
 ; i.e., exists precondition of some current action, NOT currently achieved,
 ; that has every child of a parent-link in its ancestor-set. 
; Or, more simply, variables should "die off".  
;; TODO: generalize.  This is just special case for most logistics.
(defn uses-dead-vars? [s ancestor-map]
  (let [goal-action (util/safe-singleton (state/get-var s (possible-actions-var sas/goal-var-name)))
        live-set (apply clojure.set/union #{sas/goal-var-name}
                        (for [pv (keys (dissoc (:precond-map goal-action) sas/goal-var-name))
                              :when (or (child-unavailable s pv sas/goal-var-name)
                                        (not (can-greedily-use? s goal-action pv sas/goal-var-name)))]
                          (ancestor-map pv)))
        vars     (util/safe-get ancestor-map sas/goal-var-name)]
 ;    (println live-set)
    (not-every? live-set
                (concat     ;                 (map second extra-edges)
                 (for [p vars
                       :let [a (state/get-var s (possible-actions-var p))]
                       :when (not (contains? #{#{} :wait} a))]
                   p)
                 (for [p vars
                       :let [c (state/get-var s (child-var p))]
                       :when c]
                   c)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers - Branching ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: ???
(defn possible-scheduled-side-effector? [s v side]
  (when-let [actions (state/get-var s (possible-actions-var side))]
    (and (not (#{#{} :wait} actions ))
         (some #(contains? (:effect-map %) v) actions))))

(defn guaranteed-scheduled-side-effector? [s v side]
  (when-let [actions (state/get-var s (possible-actions-var side))]
    (and (not (#{#{} :wait} actions ))
         (every? #(contains? (:effect-map %) v) actions))))


;; TODO: look at other precondition variables too?
(defn possible-children [s p child-map prevail-map auxiliary-map]
  (let [potential-children (or (when-let [c (state/get-var s (child-var p))] [c]) (child-map p))]
    (filter #(and (or (get-in prevail-map [p %]) (possible-scheduled-side-effector? s p %))
                  #_ (not (= p (auxiliary-map %))))  ;; TODO: put back
            
            (let [aux (when-let [av (auxiliary-map p)] (state/get-var s (child-var av)))]
              (if (and aux (not (= aux p)))
                (do (util/assert-is (some #{aux} potential-children))
                    [aux])
                potential-children)))))

(defn var-at-target? [s v]
  (= (state/get-var s v) (target-value s v)))

(defn blocking-set [s a e-var]
  (set (for [p (keys (dissoc (:precond-map a) e-var))
             :when (child-unavailable s p e-var)]
         p)))

;; TODO: improve
(defn prune-and-group-actions
  "Group actions by value wanted for p, ruling out illegal values (e.g., unobtainable resource vals)."
  [s p c unhappy-actions]
  (group-by #((:precond-map %) p) unhappy-actions))



(defn side-effect-free-var? [s v effect-cluster-map]
   (every? (fn [side] (guaranteed-scheduled-side-effector? s v side))
           (disj (effect-cluster-map v) v)))

(defn conflicted-effects? [s v a]
  (some #(guaranteed-scheduled-side-effector? s v %)
        (keys (dissoc (:effect-map a) v))))

;; Is there a precondition reserved for a scheduled action
;; that needs v, which is also needed for a?
(defn conflicted-precond? [s v a]
  (some #(when-let [c (state/get-var s (child-var %))]
           (let [acts (state/get-var s (possible-actions-var c))]
             (and (not (= c v)) (not (= acts :wait)) (seq acts)
                  (every? (fn [ca] (contains? (:precond-map ca) v)) acts))))        
        (keys (dissoc (:precond-map a) v))))

(defn conflicted-action? [s v a]
  (or (conflicted-effects? s v a)
      (conflicted-precond? s v a)))



(defn structural-partitions [actions]
  (map set (vals (group-by (comp util/keyset :precond-map) actions))))



;; Here, need to worry about side effects.
;; If there are cycles that do not effect the reserving action
;; TODO: dynamic determination of effect clustering, conflicts
;; NOTE: we require that possible-actions-var is correct for vars other than v,
;;  and children are correct for vars other than (into or out of) v?
;;  but state may be otherwise inconsistent.
;;  (must take care, this happens in future state currently...)
(defn make-possible-actions-fn [dtgs effect-cluster-map pre-partition? teleport-set shortest-path-fn]
  (let [simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (fn [s v cur-val dst-val]
      (let [dtg (get-in dtgs [v cur-val])
            actions (remove #(conflicted-action? s v %)
                            (if (side-effect-free-var? s v effect-cluster-map)
                              (if (contains? teleport-set v)
                                (when-not (= cur-val dst-val)
                                  [(make-teleport-action v cur-val dst-val (shortest-path-fn v cur-val dst-val))])
                                (mapcat dtg (acyclic-succ-fn v cur-val dst-val)))
                              (apply concat (vals dtg))))]
        (concat
         (when (= cur-val dst-val) [#{}])
         (when (seq actions) (if pre-partition? (structural-partitions actions) [(set actions)])))))))


(comment (util/singleton? (get effect-cluster-map v)))

;; TODO: better choice of unhappy child?
;; (NOTE -- if we're choosing on behalf of auxiliary, and all actions are happy with p's value,
;;   we MUST treat all actions as concerned -- ignoring greedy.  Just do that by default for now)
;;   TODO: investigate sometimes re-grouping happy with indifferent.
(defn bottom-up-expand-actions [s p unhappy-children child-map prevail-map auxiliary-map possible-actions-fn]
  (let [children                (possible-children s p child-map prevail-map auxiliary-map)
        c                       (first (util/intersection (set children) (set unhappy-children)))
        _ (util/assert-is (identity c) "%s" [s p unhappy-children children (do (clojure.inspector/inspect-tree (sort-by key s)) nil)])
        actions (state/get-var s (possible-actions-var c))
        [concerned indifferent] (util/separate #(contains? (:precond-map %) p) actions)
;        [happy unhappy]         (util/separate #(can-greedily-use? s % p c) concerned)
;        lazy-set                (set (concat happy indifferent))
        unhappy concerned
        lazy-set (set indifferent) ;; TODO
        ]
    (assert (= :wait (state/get-var s (possible-actions-var p))))
    (when-let [cur-c (state/get-var s (child-var p))] (assert (= cur-c c)))
;    (assert (seq unhappy)) -- can't assert with aux
    (concat
     (when (seq lazy-set)
       [(make-set-actions-action c lazy-set)])
     (for [other-c (remove #{c} children)]
       (make-set-child-action p other-c))
     (for [[p-val wanting-actions] (prune-and-group-actions s p c unhappy)
           possible-next-actions (possible-actions-fn (state/set-var s (possible-actions-var c) (set wanting-actions))
                                                      p (state/get-var s p) p-val)]
       (make-bottom-up-expand-action s p c (set wanting-actions) possible-next-actions)))))

;; NOTE: what if there are multiple actions on a var; some ready to fire, and some blocked?
;; this will be a source, but we cannot proceed.
;; need to split on this!
;; Worse, can have none greedy and ones blocked on various things.
;; Options are to split when blocking happens, always, or greedily execute just those that can.
;; TODO: think about if we should split when blocking happens
;; With part?, this is no longer an issue.
(defn greedy-fire-actions [s v possible-actions-fn]
  (let [actions-by-block (group-by #(blocking-set s % v) (state/get-var s (possible-actions-var v)))]
    (assert (or (seq (actions-by-block #{})) (> (count actions-by-block) 1)))
    (concat
     (for [[block as] (dissoc actions-by-block #{})]
       (make-set-actions-action v (set as)))
     (for [a (actions-by-block #{})
           possible-next-actions (possible-actions-fn s v (util/safe-get (:effect-map a) v) (target-value s v))]
       (make-greedy-fire-action s a v possible-next-actions)))))


;; TODO: auxiliary vars.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ASPlanEnv [base-sas-env init actions-fn g-map relevant-vars shortest-path-fn ]
  env/Env 
    (initial-state [e] init)
    (actions-fn    [e] actions-fn)
    (goal-fn       [e] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [e] g-map))

(defn print-state [s]
  (println "\n")
  (doseq [a (reverse (:act-seq (meta s)))] (println a))
  (println)
#_  (println s))

(defn inspect-state [s]
  (clojure.inspector/inspect-tree (sort-by key (state/as-map s))))


;; Hack to deal with hanging vars -- shouldn't be needed much when auxiliary handling added.
(defn rejigger-prevail-cg [prevail-cg]
  (let [sinks (util/difference (set (map second prevail-cg)) (set (map first prevail-cg)))
        bad-sinks (disj sinks sas/goal-var-name)]
    (for [[f t] prevail-cg]
      (if (bad-sinks t)
        [t f]
        [f t]))))

;; TODO: fix auxiliary var mapping.

;; TODO: improve
(defn get-auxiliary-map [sas-problem]
  (let [auxiliary-map (util/map-vals first (sas-analysis/auxiliary-vars sas-problem))]
    (assert (graphs/dag? auxiliary-map))
    auxiliary-map))




;; TODO: add assertions on precond var = effect var
;; Recall: greedy helps the most when, e.g., lots of passengers and not much room.
(defn make-asplan-env
  "Make an actino-set planning environment.  Switches are:
    check-deadlock?: check for cycles in precedence graph above and beyond lack of sources
    check-components?: check for disconnected components, rule out sources outside of goal comp
    part?: initiall partition actions based on precondition variable set."
  ([sas-problem & {:keys [directed? greedy? deadlock? dead-vars? components? part? aux? teleport?] :as m
                   :or   {directed? true greedy? true deadlock? true dead-vars? true components? false part? true aux?  true teleport? true}}]
     (assert (every? #{:directed? :greedy? :deadlock? :dead-vars? :components? :aux? :part? :teleport?} (keys m)))
     (assert (= greedy? true))
     (let [edge-rule     (if greedy? :greedy :naive)
           causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
           vars          (graphs/ancestor-set causal-graph [sas/goal-var-name])
           causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
           av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
           child-var-map (assoc (util/map-vals #(map second %) (group-by first causal-graph))
                           sas/goal-var-name [])
           prevail-cg    (sas-analysis/prevail-causal-graph sas-problem)
;           tsi           (graphs/df-topological-sort-indices causal-graph) ;; TODO: doesn't seem to matter...
           tsi           (graphs/df-topological-sort-indices (rejigger-prevail-cg prevail-cg)) ;; way worse.
           prevail-cvm   (util/map-vals #(util/intersection (set %) vars)
                                        (graphs/edge-list->outgoing-map prevail-cg))
           
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           effect-cluster-map (into {} (for [cluster (sas-analysis/effect-clusters sas-problem), v cluster] [v cluster]))
           shortest-path-fn (make-shortest-path-fn dtgs)
           teleport-vars    (if teleport?
                              (util/difference (set (map first causal-graph)) (set (map second causal-graph)))
                              #{})           
           possible-actions-fn (make-possible-actions-fn dtgs effect-cluster-map part?
                                                         teleport-vars shortest-path-fn)

           auxiliary-map (if aux? (get-auxiliary-map sas-problem) {})
           canonicalize  (fn [s bu-map]
                           (reduce (fn [bum k]
                                     (if-let [nk (auxiliary-map k)]
                                       (let [nkc (state/get-var s (child-var nk))]
                                         (if (not nkc)
                                           (assoc (dissoc bum k) nk (util/union (get bum k) (get bum nk #{})))
                                           (if (some #{nkc} (get bum k))
                                             (assoc bum k #{nkc})
                                             (dissoc bum k))))
                                       bum))
                                   (util/map-vals set bu-map) (keys bu-map)))

           ] 
;       (assert (graphs/dag? causal-graph))    
                                        ;       (assert (sas-analysis/unary? sas-problem))
       (println tsi "\n" auxiliary-map)
       (doseq [a (:actions sas-problem)]
         (when-not (every? (partial contains? (:precond-map a)) (keys (:effect-map a)))
           (println (:name a) (apply dissoc (:effect-map a) (keys (:precond-map a))))))       
       (doseq [a (:actions sas-problem)]
         (assert (every? (partial contains? (:precond-map a)) (keys (:effect-map a)))))
       
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) vars (goal-action dtgs))

        (fn asplan-actions [s]
          (util/do-debug 2 (print-state s) (Thread/sleep 100))
          (if (and dead-vars? (uses-dead-vars? s av-map ))
            (do (util/print-debug 1 "Pruning due to dead vars") nil)
            (let [sources-by-type (source-vars-by-type s vars deadlock? components? )]
;              (println sources-by-type)
              (if sources-by-type
                (util/prln-debug 2
                 (util/cond-let [sources]
                  (seq (get sources-by-type :greedy))
                  (greedy-fire-actions s (first sources) possible-actions-fn)

                  (seq (canonicalize s (get sources-by-type :bottom-up)))
                  (let [_ (println (map first sources))
                        [p-var children] (apply max-key (comp tsi first) sources)] 
                    (bottom-up-expand-actions s p-var children child-var-map prevail-cvm auxiliary-map possible-actions-fn)) 
               
                  :else (do (util/assert-is (empty? (:other sources-by-type))
                                            "%s" [(do (print-state s) (inspect-state s)
                                                      s)])
                            (util/print-debug 1 "Pruning since nothing to do?!"))))
               
               (util/print-debug 1 "Pruning due to deadlock")))))
        
        
        (env/goal-map sas-problem)
        vars shortest-path-fn))))


(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) sol)))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Fancier search ;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Just hte cost of committed actions
(defn make-committed-actions-heuristic [vars]
  (fn [s]
    (reduce + (for [v vars
                    :let [val (state/get-var s (possible-actions-var v))]
                    :when (and (not (= :wait val)) (seq val))]
                (apply min (map :reward val))))))

;; Committed actions + shortest paths to target values.
;; could also maybe include reserved but not scheduled..
(defn make-domain-paths-heuristic [vars shortest-path-fn]
  (fn [s]
    (reduce + (for [v vars
                    :let [acts (state/get-var s (possible-actions-var v))]
                    :when (and (not (= :wait acts)) (seq acts))]
                (apply min (map #(+ (:reward %)
                                    (shortest-path-fn v (get (:effect-map %) v) (target-value s v)))
                                acts))))))

;; Committed actions + shortest paths + matching for preconds.
(defn all-committments-heuristic [s]
  0)

(defn canonicalize-state [s vars]
  (for [v vars] (state/get-var s v)))

;; Keeps a separate closed list for canonical state pruning.
(defn asplan-search
  ([env] (asplan-search env (constantly 0)))
  ([env h-type]
     (let [q       (queues/make-graph-search-pq)
           actions (env/actions-fn env) 
           goal    (env/goal-fn env)
           init    (env/initial-state env)
           closed  (HashMap.)
           relevant-vars    (:relevant-vars env)
           shortest-path-fn (:shortest-path-fn env)
           heuristic (case h-type
                       :actions (make-committed-actions-heuristic relevant-vars)
                       :paths   (make-domain-paths-heuristic relevant-vars shortest-path-fn))]
        (queues/pq-add! q init (heuristic init))
        (loop []
          (when-not (queues/pq-empty? q)
            (let [[s c] (queues/pq-remove-min-with-cost! q)
                  s-r     (or (:reward (meta s)) 0)
                  canon-s (canonicalize-state s relevant-vars)
                  canon-r (get closed canon-s Double/NEGATIVE_INFINITY)]
              (util/print-debug 3 "dequeueing " (:act-seq (meta s)) c s "\n")
              (or (and (goal s) [(asplan-solution-name (reverse (:act-seq (meta s))))
                                 (:reward (meta s)) #_ (println s)])
                  (if (< s-r canon-r)
                    (recur)
                    (do
                      (when (> s-r canon-r) (.put closed canon-s s-r))
                      (let [acts (actions s)]
                        (util/print-debug 4 "Actions are:" (map env/action-name acts) "\n")
                        (util/print-debug 4 (for [a acts :when (not (env/applicable? a s))] (str (:name a) (:precond-map a) "not applicable" )))
                        (doseq [a acts :when (env/applicable? a s)]
                          (let [[ss sc] (env/successor a s)
                                f-val (+ (:reward (meta ss)) (heuristic ss))]
                            (when (> f-val Double/NEGATIVE_INFINITY)
                              #_(util/print-debug 1 "warning: pruning " ss)
                              (queues/pq-add! q ss (- 0 f-val ))))))
                      (recur))))))))))


;; (do (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util 'angelic.sas.hm-heuristic 'angelic.search.interactive) (require '[angelic.search.action-set.asplan :as ap] '[angelic.search.action-set.gasplan2 :as gap2] '[angelic.search.action-set.asplan-r :as rap]))

;; (let [e (force (nth ipc2-logistics 5)) ]  (println (time (run-counted #(ap/asplan-solution-pair-name (uniform-cost-search (ap/make-asplan-env e ))))))  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))) (println (time (run-counted #(gap2/asplan-solution-pair-name (uniform-cost-search (gap2/make-asplan-env e )))))))

;; (let [e (force (nth ipc2-logistics 7)) ]  (println (time (run-counted #(ap/asplan-solution-pair-name (uniform-cost-search (ap/make-asplan-env e ))))))  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))) (println (time (run-counted #(gap2/asplan-solution-pair-name (uniform-cost-search (gap2/make-asplan-env e )))))))

;; (let [e (force (nth ipc2-logistics 5)) ]  (println (time (run-counted #(uniform-cost-search e ))))  (println (time (run-counted #(gap/asplan-solution-pair-name (uniform-cost-search (gap/make-asplan-env e )))))) (println (time (run-counted #(gap2/asplan-solution-pair-name (uniform-cost-search (gap2/make-asplan-env e )))))))

;; (let [e (second  (nth (sas-sample-problems 0) 11)) ] (println (time (debug 0 (run-counted #(gap2/asplan-solution-pair-name (interactive-search (gap2/make-asplan-env e ))))))))

;; (let [e (second  (nth (sas-sample-problems 0) 11)) ]  (println (time (run-counted #(uniform-cost-search e ))))   (println (time (run-counted #(rap/asplan-solution-pair-name (uniform-cost-search (rap/make-asplan-env e (fn [v] (= (first v) :capacity)) #{:drop} ))))))  (println (time (debug 0 (run-counted #(gap2/asplan-solution-pair-name (uniform-cost-search (gap2/make-asplan-env e ))))))))

;; (let [e @(nth ipc2-logistics 10) ] #_ (println (time (run-counted #(uniform-cost-search e ))))     (println (time (debug 0 (run-counted #(gap2/asplan-search (gap2/make-asplan-env e :aux? true) :paths))))))