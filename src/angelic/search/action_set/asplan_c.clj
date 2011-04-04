(ns angelic.search.action-set.asplan-c
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


;; "effect-clustered" Version of asplan for cyclic domains.
;; Basic idea: cluster variables so that all vars effected by any action live in
;; the same cluster.
;; Each cluster is treated like a variable, and we run asplan.
;; Complication is that we don't want to explode domains,
;; so we need to reason about variables with "factored" domains.

;; Since most of leverage is for roots like trucks,
;; we treat these specially with state abstraction, solve and cache shortest
;; paths and teleport right to goal.
;; (TODO).  if leaves are clustered, need multiple goal states -- see if
;; worth supporthing this case or not.  

;; TODO: cluster successor generators?
;; TODO: state abstraction.

;; meta-vars are defined on clusters.
;; Clusters are single vars or sets of vars (or always sets?)

;; Interesting question: when doing directed work on a cluster,
;; do we always freeze on the combination wanted by child? seems so.
;; Note child relationship can correspond to multiple variable preconditions.

;; Notation is still kind of screwy, in that clusters are refered to as "v" or "variable" from copy-paste.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Map from variable to cluster containing it (or nil if singleton?)


(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

;; Action vars have a special value, :frozen, meaning that current value must be used
;; by child.  Only really useful 
(defn action-var [v]       (assert (set? v)) [:action v])
(defn free-var [v]         (assert (set? v))[:free? v])
(defn parent-var [v child] (assert (set? v)) (assert (set? child)) [:parent? v child])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a child (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init clusters child-var-map goal-action]
  (state/set-vars init
    (concat 
     (apply concat
            (for [var clusters]
              (concat [[(action-var var) nil] [(free-var var) true]]
                      (for [c (child-var-map var)] [(parent-var var c) false]))))
     [[(action-var #{sas/goal-var-name}) goal-action]])))

;; All of these now take clusters.

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

(defn make-add-action-action [var->cluster {:keys [name precond-map effect-map reward] :as factored-primitive}]
  (util/sref-set! *add-count* (inc (util/sref-get *add-count*)))
  (let [cluster (var->cluster (first (keys effect-map)))]
    (env-util/make-factored-primitive
     [::AddAction name]
     (assoc (select-keys precond-map cluster) (action-var cluster) nil)
     {(action-var cluster) factored-primitive}
     reward)))

(defn make-set-parent-var-action [p-var c-var]
  (env-util/make-factored-primitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


(defn make-fire-action
  "Simple version of greedy-fire, used for exhaustive action list. (No add-parent)."
  [var->cluster {:keys [name precond-map effect-map reward] :as factored-primitive}]
  (let [cluster      (var->cluster (first (keys effect-map)))
        precond-clusters (map var->cluster (keys (apply dissoc precond-map cluster)))]
    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var cluster) factored-primitive]]
                   (for [v precond-clusters] [(parent-var v cluster) true])
                   (for [v precond-clusters] [(action-var v) :frozen])))
     (into effect-map 
           (concat [[(action-var cluster) nil]]
                   (for [v precond-clusters] [(free-var v)              true])
                   (for [v precond-clusters] [(parent-var v cluster) false])
                   (for [v precond-clusters] [(action-var v) nil])))
     0)))


;; TODO: should fail if I own parent, it has right value, but an action. (right now, we assert)...
;; Try to make an action that greedily fires the action scheduled on effect-var,
;; effectively representing a composition of set-parent and fire-action actions.
;; Note that this avoids some (unnecessary) branching on children of parent vars.
;; Assumes this will always be called on a "source", and asserts correspondingly.
(defn make-greedy-fire-action [s var->cluster cluster]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> cluster action-var (state/get-var s))
        precond-clusters (map var->cluster (keys (apply dissoc precond-map cluster)))
        [free-pc unfree-pc] (util/separate #(state/get-var s (free-var %)) precond-clusters)]
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-clusters))    
    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var cluster) factored-primitive]]
                   (for [v free-pc]   [(free-var v)              true])
                   (for [v unfree-pc] [(parent-var v cluster) true])
                   (for [v precond-clusters] [(action-var v) (state/get-var s (action-var v))])))           
     (into effect-map 
           (concat [[(action-var cluster) nil]]
                   (for [v unfree-pc] [(free-var v)              true])
                   (for [v unfree-pc] [(parent-var v cluster) false])
                   (for [v precond-clusters] [(action-var v) nil])))
     0)))


(defn make-fire-action-type [s edge-rule var->cluster cluster]
  (doto (case edge-rule
          :naive (make-fire-action var->cluster (->> cluster action-var (state/get-var s)))
          :greedy (make-greedy-fire-action s var->cluster cluster))
     (-> (env/applicable? s) assert))) ;; TODO: comment out!!



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
  [s var->cluster child-map rule]
  (apply concat
         (for [v (keys child-map)]
           (let [a (state/get-var s (action-var v))]
             (cond
               (nil? a)      nil
               (= :frozen a) (when-let [c (current-child s child-map v)] [[c v]])
               :else         (remove nil?
                               (for [[p pval] (apply dissoc (util/safe-get a :precond-map) v)]
                                 (let [right-val? (= (state/get-var s p) pval)
                                       p-cluster  (var->cluster p)
                                       p-child    (current-child s child-map p-cluster)
                                       unavail?   (not (or (= p-child nil) (= p-child v)))]
                                  (case rule
                                    :naive  (cond unavail?         [p-child v]
                                                  (or (not (= p-child v)) (not (= (state/get-var s (action-var p-cluster)) :frozen))) [p-cluster v])
                                    :greedy (cond unavail?         [p-child v]
                                                  (not right-val?) [p-cluster v]))))))))))




(defn source-clusters
  "Take the graph from var-ordering-edges, and return the sources in the same component
   as the goal variable, which are ripe for action.  Returns nil if there are any cycles
   in the graph, since this indicates a deadlock (at least some actions cannot fire)."
  [s var->cluster child-map check-deadlock? check-components? edge-rule]
;  (println (var-ordering-edges s child-map rule))
  (let [edges (doall (var-ordering-edges s var->cluster child-map edge-rule))]
    (assert (every? set? (apply concat edges))) ;; TODO: Remove
    (assert (every? #(not (apply = %)) edges))   ;; remove
    (when (or (not check-deadlock?) (graphs/dag? edges)) 
      (let [sources (clojure.set/difference (set (cons #{sas/goal-var-name} (map first edges))) (set (map second edges)))
            goal-component-sources
            (if check-components?
              (clojure.set/intersection
               sources
               (graphs/ancestor-set (cons [#{sas/goal-var-name} #{sas/goal-var-name}] edges) [#{sas/goal-var-name}]))
              sources)]
        (when-not (= (count sources) (count goal-component-sources)) (println "Warning: multiple components..."))
        (when check-deadlock? (assert (seq goal-component-sources)))
        goal-component-sources))))

(defn source-cluster-type [s child-map v]
  (let [a (state/get-var s (action-var v))]
    (cond (= a :frozen)  :top-down-activate
          a              :fire
          ;; no action
          (not (state/get-var s (free-var v))) :bottom-up-action 
          (some (fn [c] (when-let [ca (state/get-var s (action-var c))]
                          (some v (keys (:precond-map ca)))))
                (child-map v))
                         :bottom-up-activate
          :else          :top-down-action)))

;; TODO: dynamic bottom-up pruning.
;; i.e., exists precondition of some current action, NOT currently achieved,
;; that has every child of a parent-link in its ancestor-set. 
;; Or, more simply, variables should "die off".  
;; TODO: generalize.  This is just special case for most logistics.
(defn uses-dead-clusters? [s var->cluster ancestor-map child-map extra-edges]
  (let [gpm      (:precond-map (state/get-var s (action-var #{sas/goal-var-name})))
        live-set (apply clojure.set/union #{#{sas/goal-var-name}}
                        (for [pv (remove #{sas/goal-var-name} (keys gpm))
                              :when (not (= (state/get-var s pv) (gpm pv)))]
                          (ancestor-map (var->cluster pv))))]
    (not-every? live-set
                (concat (map second extra-edges)
                        (for [p (keys child-map)
                              :let [a (state/get-var s (action-var p))]
                              :when (and a (not (= a :frozen)))]
                          p)
                        (for [[p cs] child-map, c cs
                              :when (state/get-var s (parent-var p c))]
                          c)))))


(defn activation-actions  "Return a list of all activation actions for cluster v"
  [child-map v]
  (for [c (child-map v)]
    (make-set-parent-var-action v c)))

(defn add-actions [s c var->cluster cluster-sgs]
  (cons (make-freeze-var-action c)
        (for [a ((cluster-sgs c) s)]
          (make-add-action-action var->cluster a))))

;; TODO: "state abstraction" here for single clusters.
;; TODO: can we provide some notion of relevance/directedness within a cluster?
;;       i.e., may have actions affecting A & B or B & C.  If precond on C, ... ?
(defn add-directed-actions [s c var->cluster cluster-sgs dtgs ccm acyclic-succ-fn]
  (if-let [v (util/singleton c)]
    (let [c-val (state/get-var s v)
          dtg   (get-in dtgs [v c-val])
          child (current-child s ccm c)
          d-val (-> (state/get-var s (action-var child)) :precond-map (get v))]
      (if d-val 
        (if (= c-val d-val)
          [(make-freeze-var-action c)]
          (for [n-val (acyclic-succ-fn v c-val d-val), a (dtg n-val)]
            (make-add-action-action var->cluster a)))
        (add-actions s c var->cluster cluster-sgs))) ;; only for cyclic domains -- TODO: remove?
    (let [child-action (state/get-var s (action-var (current-child s ccm c)))
          restricted-pm (select-keys (:precond-map child-action) c)]
      (cond (empty? restricted-pm) (add-actions s c var->cluster cluster-sgs) ;; for cyclic ?
            (state/state-matches-map? s restricted-pm) [(make-freeze-var-action c)]
            :else (for [a ((cluster-sgs c) s)] (make-add-action-action var->cluster a))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ASPlanEnv [base-sas-env init actions actions-fn g-map]
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
  ([sas-problem & {:keys [directed? greedy? deadlock? dead-vars? components?] :as m
                   :or   {directed? true greedy? true deadlock? true dead-vars? true components? false}}]
     (assert (every? #{:directed? :greedy? :deadlock? :dead-vars? :components?} (keys m)))
     (let [edge-rule     (if greedy? :greedy :naive)
           cluster-cg    (remove #(apply = %) (sas-analysis/effect-clustered-causal-graph sas-problem))
           clusters      (graphs/ancestor-set cluster-cg [#{sas/goal-var-name}])
           cluster-cg    (filter (fn [[c1 c2]] (and (clusters c1) (clusters c2))) cluster-cg)
           cluster-map   (util/for-map [c clusters, v c] v c)
           var->cluster  #(util/safe-get cluster-map %)
           cluster-sgs   (util/for-map [[cluster cluster-actions]
                                          (dissoc (group-by (comp cluster-map first keys :effect-map) (:actions sas-problem)) nil)]
                           cluster (sas/make-simple-successor-generator (seq cluster) cluster-actions))
           tsi           (graphs/df-topological-sort-indices cluster-cg) ;; TODO: doesn't seem to matter...
           ac-map        (util/for-map [c clusters] c (graphs/ancestor-set cluster-cg [c]))
           cc-map        (assoc (util/map-vals #(map second %) (group-by first cluster-cg))
                           #{sas/goal-var-name} [])
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)           
           acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
;       (assert (graphs/dag? causal-graph))    
;       (assert (sas-analysis/unary? sas-problem))
       (assert (contains? clusters #{sas/goal-var-name}))
       (assert (= (util/keyset cluster-map)
                  (graphs/ancestor-set (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
                                       [sas/goal-var-name])))

       ;;     (doseq [a (:actions sas-problem)] (assert (every? #(contains? (:precond-map a) %) (keys (:effect-map a)))))
       ;; TODO: Need this for real generalization, here it only has to be true on cluster!
       (doseq [a (:actions sas-problem)] (assert (some (var->cluster (first (keys (:effect-map a))))
                                                        (keys (:precond-map a)))))
       (doseq [c clusters] (println c))
       (println )
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) clusters cc-map (goal-action dtgs))
        :dummy
        (fn asplan-actions [s]
          (when-let [sources (and (or (not dead-vars?) (not (uses-dead-clusters? s var->cluster ac-map cc-map []))) 
                                  (seq (source-clusters s var->cluster cc-map deadlock? components? edge-rule)))]
            (let [sources-by-type (group-by #(source-cluster-type s cc-map %) sources)]
;;              (println sources-by-type)
              (util/cond-let [sources]
                (seq (sources-by-type :fire))
                [(make-fire-action-type s edge-rule var->cluster (first sources))]

                (seq (sources-by-type :bottom-up-action))
                (if directed?
                  (add-directed-actions s (apply min-key tsi sources) var->cluster cluster-sgs dtgs cc-map acyclic-succ-fn)
                  (add-actions s (apply min-key tsi sources) var->cluster cluster-sgs))               
                     
                (seq (sources-by-type :bottom-up-activate))
                (activation-actions cc-map (apply max-key tsi sources)) ;; TODO: smarter sort!
                
                (seq (sources-by-type :top-down-activate))
                (do (println "I!") (activation-actions cc-map (first sources)))
                
                (seq (sources-by-type :top-down-action))
                (do (println "A!") (add-actions s (first sources) var->cluster cluster-sgs))
                
                :else (assert "Unknown source type!")))))
        (env/goal-map sas-problem)))))





(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) sol)))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])




;; TODO: cutoff when top-down and bottom-up meet, don't match ? (or earlier)

;; TODO: Take advantage of "greedy-chain" condition, don't assign


;; (do (require '[angelic.search.action-set.asplan-c :as ac]) (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util))

;; no clusters---
;; (let [e (force (nth ipc2-logistics 5)) ] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(ac/asplan-solution-pair-name (uniform-cost-search (ac/make-asplan-env e)))))))

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


 ; (doseq [[alg sp]  [[make-asplan-env asplan-solution-pair-name] [angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name]] ] (println (time (run-counted #(sp (uniform-cost-search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))

; (-> (nth (vals (sas-sample-files 1)) 5) make-sas-problem-from-pddl unarize make-asplan-env interactive-search)



