(ns angelic.search.action-set.asplan-r
  (:require [angelic.util :as util]
            [angelic.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis])
  (:import [java.util HashMap HashSet]))


;; Version of asplan that can handle acyclic domains with resources.

;; Basic idea:
;; - Remove incoming edges in CG from resource var.
;; Secondary:
;; - Group action commitments, pick resource val just in time.

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
  (assert nil)
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
  (let [{:keys [name precond-map effect-map reward resource-map] :as factored-primitive}
          (->> effect-var action-var (state/get-var s))
        [r-var r-val-map] resource-map
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
    (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars)
    (when r-var (util/assert-is (contains? r-val-map (state/get-var s r-var)) "%s" [s factored-primitive (def *bad* s)]))
    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var effect-var) factored-primitive]]
                   (when r-var [[r-var (state/get-var s r-var)]])
                   (for [v free-pv]   [(free-var v)              true])
                   (for [v unfree-pv] [(parent-var v effect-var) true])
                   (for [v precond-vars] [(action-var v) (state/get-var s (action-var v))])))           
     (into effect-map 
           (concat [[(action-var effect-var) nil]]
                   (when r-var [[r-var (util/safe-get r-val-map (state/get-var s r-var))]])
                   (for [v unfree-pv] [(free-var v)              true])
                   (for [v unfree-pv] [(parent-var v effect-var) false])
                   (for [v precond-vars] [(action-var v) nil])))
     0)))

(defn make-sloppy-fire-action [s effect-var]
  (assert nil)
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
  [s child-map r-own-map resource-decrease-prefix-set rule]
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
                                                  (or (not (= p-child v)) (not (= (state/get-var s (action-var p)) :frozen))) [p v])
                                    :greedy (cond unavail?         [p-child v]
                                                  (not right-val?) [p v]
                                                  (and (not p-child) (= p (r-own-map (first (:resource-map a))))
                                                       (not (resource-decrease-prefix-set (first (:name a)))))
                                                  [p v])
                                    :sloppy (cond (and unavail? (or (not right-val?) (when-let [a (state/get-var s (action-var p))] (not (= a :frozen)))))         [p-child v]
                                                  (and (not unavail?) (not right-val?)) [p v])
                                    :extra-sloppy
                                            (cond (and unavail? (not right-val?)) [p-child v]
                                                  (and (not unavail?) (not right-val?)) [p v]))))))))))




(defn source-vars
  "Take the graph from var-ordering-edges, and return the sources in the same component
   as the goal variable, which are ripe for action.  Returns nil if there are any cycles
   in the graph, since this indicates a deadlock (at least some actions cannot fire)."
  [s child-map check-deadlock? check-components? r-own-map resource-decrease-prefix-set edge-rule ]
;  (println (var-ordering-edges s child-map rule))
  (let [edges (doall (var-ordering-edges s child-map r-own-map resource-decrease-prefix-set edge-rule))]
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

;; TODO: generalize?!
(defn action-matches? [p v a]
  (let [n (:name a)]
    (or (not (#{:pick-up :drop} (first n)))
        (= (second p) (second n)))))


(defn activation-actions  "Return a list of all activation actions for var v"
  [s child-map rvm v]
  (let [resource-vars (rvm v)]
    (for [c (child-map v)
          :when 
          (or (not (seq resource-vars))
              (let [cav (state/get-var s (action-var c))]
                (or (not cav) (= :frozen cav)
                    (let [[arvar arval-map] (:resource-map cav)]
                      (and (action-matches? v c cav)
                           (or (not (contains? resource-vars arvar))
                               (contains? arval-map (state/get-var s arvar))))))))]
      (make-set-parent-var-action v c))))

(defn add-actions [s v dtgs]
  (cons (make-freeze-var-action v)
        (for [as (vals (get-in dtgs [v (state/get-var s v)])), a as]
          (make-add-action-action a))))

(defn add-directed-actions [s v dtgs cvm r-own-m acyclic-succ-fn]
  (let [c-val (state/get-var s v)
        dtg   (get-in dtgs [v c-val])
        child (current-child s cvm v)
        d-val (-> (state/get-var s (action-var child)) :precond-map (get v))]
    ;;    (when greedy? #_ (util/assert-is (not (= c-val d-val)) "%s" (def *s* s)))
    (filter
     (fn [a]
       (let [a (first (vals (:effect-map a)))]
         (and #_ (or (not (#{:pick-up :drop} (first (:name a))))
                  (every? (fn [v2] (or (not (= (current-child s cvm v2) v))
                                       (= (second v2) (second (:name a)))))
                          (keys cvm)))
              (let [[r-var r-val-map] (:resource-map a)]
                (or (not r-var)
                    (not (= (current-child s cvm (util/safe-get r-own-m r-var)) v))
                    (contains? r-val-map (state/get-var s r-var)))))))     
     (if (= c-val d-val)
       [(make-freeze-var-action v)]
       (for [n-val (acyclic-succ-fn v c-val d-val), a (dtg n-val)]
         (make-add-action-action a))))))




(comment ; Dead-end check moved out to init.
 (defn possible-activation-actions  
   "Return a list of possible activation actions for var v possible in state s.
   To be possible parent, must be supported from below. "
   [s ancestor-map child-map v]
                                        ;   (activation-actions child-map v) #_   
   (for [c (child-map v) :when (not (or (dead-end? s ancestor-map child-map [[ v c]])))]
     (make-set-parent-var-action v c))))
;   (or (deadlocked? s child-map [[v c]]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;; Resource transformation ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn constrain-drops [sas-problem resource-var? drop-name]
  (let [actions (:actions sas-problem)
        g (util/safe-singleton (filter #(= (:name %) sas/goal-action-name) actions))]
    (sas/make-sas-problem
     (:vars sas-problem)
     (:init sas-problem)
     (remove
      (fn [a]
        (and (= (first (:name a)) drop-name)
             (let [[evar eval] (util/safe-singleton (filter #(not (resource-var? (key %))) (:effect-map a)))]
               (not (= eval (util/safe-get (:precond-map g) evar))))))
      actions))))


(defn resource-simplify [actions resource-var?]
  (util/assert-is (graphs/dag? (remove #(resource-var? (first %)) (sas-analysis/standard-causal-graph {:actions actions}))))
  (let [final-actions-by-pe (HashMap.)
        resource-owners     (HashMap.)        
        resource-edges      (HashSet.)
        add-a! (fn [precond-map effect-map rv a]
                 (let [k [precond-map effect-map rv]]
                   (.put final-actions-by-pe k (cons a (.get final-actions-by-pe k)))))]
    (doseq [a actions]
      (let [{:keys [name precond-map effect-map reward]} a
            resource-vars (filter resource-var? (keys effect-map))]
        (case (count resource-vars)
          0 (add-a! precond-map effect-map nil a)
          1 (let [resource-var (first resource-vars)
                  pre-r  (util/safe-get precond-map resource-var)
                  eff-r  (util/safe-get effect-map resource-var)
                  rpm    (dissoc precond-map resource-var)
                  rem    (dissoc effect-map resource-var)
                  evar   (util/safe-singleton (keys rem))
                  owner  (util/safe-singleton (keys (dissoc rpm evar)))]
              (.add resource-edges [resource-var evar])
              (if-let [o (.get resource-owners resource-var)]
                (assert (= o owner))
                (.put resource-owners resource-var owner))
              (add-a! rpm rem resource-var
                      (assoc a :precond-map rpm :effect-map rem
                             :resource-map [resource-var {pre-r eff-r}]))))))
    [(doall
      (for [[[pm em] as] (seq final-actions-by-pe)]
        (or (util/singleton as)
            (let [resource-maps (map :resource-map as)]
              (util/assert-is (every? identity resource-maps) "%s" as)
              (assert (apply = (map :reward as)))
              (util/assert-is (apply = (map first resource-maps)))
              (assoc (first as) :resource-map
                     [(ffirst resource-maps) (reduce util/merge-disjoint (map second resource-maps))])))))
     (into {} resource-owners)
     (seq resource-edges)]))


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
;; Note: resources get totally removed from ...
(defn make-asplan-env
  "Make an actino-set planning environment.  Switches are:
    check-deadlock?: check for cycles in precedence graph above and beyond lack of sources
    check-components?: check for disconnected components, rule out sources outside of goal comp
    edge-rule: :naive, :greedy, :sloppy, or :extra-sloppy.
       Naive means we stick exactly to the simple semantics of the vanilla actions.
       Greedy means we forget about reserving preconditions when free and we can fire right now (less branching).
       Sloppy means we ignore if preconditions are free, but require no action on them.
       Extra-sloppy means anything goes -- if you can execute ignoring commitments, go for it."
  ([sas-problem resource-var? resource-decrease-prefix-set
    & {:keys [directed? greedy? deadlock? dead-vars? components?] :as m
       :or   {directed? true greedy? true deadlock? true dead-vars? true components? false}}]
     (assert (every? #{:directed? :greedy? :deadlock? :dead-vars? :components?} (keys m)))
     (let [edge-rule     (if greedy? :greedy :naive)
           [actions r-own-m] (resource-simplify (:actions sas-problem) resource-var?)
           rvm           (util/map-vals #(set (map key %)) (group-by val r-own-m))
           sas-problem   (assoc sas-problem :actions actions)
           causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
           vars          (graphs/ancestor-set causal-graph [sas/goal-var-name])
           causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
           tsi           (graphs/topological-sort-indices causal-graph)
           av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
           child-var-map (assoc (util/map-vals #(map second %) (group-by first causal-graph))
                           sas/goal-var-name [])
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
           acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
        :dummy
        (fn asplan-actions [s]
          (when-let [sources (and (or (not dead-vars?) (not (uses-dead-vars? s av-map child-var-map []))) 
                                  (seq (source-vars s child-var-map deadlock? components? r-own-m resource-decrease-prefix-set edge-rule)))]
            (let [sources-by-type (group-by #(source-var-type s child-var-map %) sources)]
;;              (println sources-by-type)
              (util/cond-let [sources]
                (seq (sources-by-type :fire))
                [(make-fire-action-type s  edge-rule (first sources))]

                (seq (sources-by-type :bottom-up-action))
                (if directed?
                  (add-directed-actions s (apply min-key tsi sources) dtgs child-var-map r-own-m acyclic-succ-fn)
                  (add-actions s (apply min-key tsi sources) dtgs))               
                     
                (seq (sources-by-type :bottom-up-activate))
                (activation-actions s child-var-map rvm (apply max-key tsi sources)) ;; TODO: smarter sort!

                ;; TODO: handle resources here!
                (seq (sources-by-type :top-down-activate))
                (do (println "I!") (activation-actions child-var-map (first sources)))
                
                (seq (sources-by-type :top-down-action))
                (do (println "A!") (add-actions s (first sources) dtgs))
                
                :else (assert "Unknown source type!")))))
        (env/goal-map sas-problem)
        causal-graph dtgs av-map child-var-map tsi acyclic-succ-fn))))
;; TODO: remove irrelelvant resources
;; TODO: problem is these domains are like taxi without constraint.
;; TODO: another problem for, e.g., gripper is that location gets encoded with free.

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



;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util 'angelic.sas.hm-heuristic)

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


 ; (doseq [[alg sp]  [[make-asplan-env asplan-solution-pair-name] [angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name]] ] (println (time (run-counted #(sp (uniform-cost-search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))

; (-> (nth (vals (sas-sample-files 1)) 5) make-sas-problem-from-pddl unarize make-asplan-env interactive-search)
