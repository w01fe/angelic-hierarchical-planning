(ns angelic.search.action-set.asplan2
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


;; New version.
;; Instead of choosing actions, together choose:
;;   set of child intentions (all succeed or single failure), next value for each child variable.
;; (next value can be left abstract, ignore this possibility for now.
;; This can't work.

;; Instead, we can do:
;;  choose an action set, narrow it.
;;  note: being blocked does not change the set.
;;  set is applicable iff there exists an action in the set with a precondition
;;  that is neither blocked nor reserved.
;;  actions with no preconditions are always immediately fired, don't live in the set.

;; First incarnation just for unary domains

;; TODOS:
;; - multiple effects
;; - Possible next children (i.e., blocks held)
;; - Auxiliary variables
;; - Top-down mode?
;; ...
;; - Hueristic costs.
;; Focusing on fail-fast case (repairing blocks).

;; Investigate simply not-x choice.
;; Means even bigger state space, hopefully not that big since we get to choose how to explore.


;; Note: not actually possible always to reserve all preconds at once.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; States, (meta)primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn goal-action [dtgs]
  (-> dtgs
      (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
      util/safe-singleton))

(defn target-var [v] [:target v])
(defn possible-parent-var [p c]  [:parent? p c])
(defn possible-actions-var [v]  [:actions v])

(defn expand-initial-state 
  "Expand the initial state with lots more stuff.  Each var can be free, OR
   have a child (in which case it must eventually be used to fire an active action on
   that var), AND in such a case, it can also have an active action to help achieve that val.
   (which changes only that var)."
  [init child-var-map]
  (let [vars (state/list-vars init)]
    (state/set-vars init
      (concat 
       (for [var vars] [(target-var v) nil])
       (for [[p cs] child-var-map, c cs] [(possible-parent-var p c) true])
       [[(target-var sas/goal-var-name) sas/goal-true-val]]))))




(defn action-effect-var [a] (util/safe-singleton (keys (:precond-map a))))





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



(defn make-greedy-fire-action [s firing-seq]
  (doseq [[a1 a2] (partition 2 1 firing-seq)]
    (let [v1 (action-effect-var a1)]
      (assert (= (state/get-var s v1) (state/get-var s (target-var v1)) ((:precond-map a2) v1)))))
  (assert (env/state-matches-map? s (apply util/merge-agree (map :precond-map firing-seq))))  
  (env-util/make-factored-primitive
   (vec (cons ::Fire (map :name firing-seq)))
   (apply util/merge-agree (map :precond-map firing-seq))
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

  
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
        (->> effect-var action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars))
#_    (util/assert-is (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars)
                    "%s" [name precond-map effect-map s])    
))


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


(defn allowed-action? [s a effect-var]
  (assert (= effect-var (util/safe-singleton (keys (:effect-map a)))))
  (every?
   (fn [v]
     (when (state/get-var s (possible-parent-var v effect-var))
       (assert (not (state/get-var s (target-var v))))
       true))   
   (keys (:precond-map a))))

(defn greedy-action? [s a] (state/state-matches-map? s (:precond-map a)))


;; if a var is actually assigned and has a target and its value is right, ...
(defn fire-sequences [s v])





(defn bottom-up-actions [s v cvm dtgs acyclic-succ-fn]
  (let [cur-val (state/get-var s v)
        dst-val (state/get-var s (target-var v))
        [greedy-actions ungreedy-actions] (->> (acyclic-succ-fn v cur-val dst-val)
                                               (map (dtgs v cur-val))
                                               (apply concat)
                                               (filter #(allowed-action? s % v) )
                                               (util/separate greedy-action?))]
    (assert dst-val)
    (assert (not (= cur-val dst-val)))
    (concat
     (intentional-actions s ungreedy-actions)
     (for [a greedy-actions, fs (fire-sequences s a)]
       (make-greedy-fire-action s fs)))))





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
                                                  (or (not (= p-child v)) (not (= (state/get-var s (action-var p)) :frozen))) [p v])
                                    :greedy (cond unavail?         [p-child v]
                                                  (not right-val?)
                                                  #_(when-not (some #(let [c (current-child s child-map %)]
                                                                     (not (or (= p-child nil) (= p-child v))))
                                                                  (keys (dissoc (:precond-map a) v)))
                                                    [p v])  ;; TODO: put back?

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
           tsi           (graphs/df-topological-sort-indices causal-graph) ;; TODO: doesn't seem to matter...
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




;; TODO: cutoff when top-down and bottom-up meet, don't match ? (or earlier)

;; TODO: Take advantage of "greedy-chain" condition, don't assign



;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util 'angelic.sas.hm-heuristic)

;; (let [e (make-random-infinite-taxi-sas2 4 4 4 2)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))

;; (let [i 25] (let [e (make-random-infinite-taxi-sas2 3 3 3 i) ae (make-asplan-env e)]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted (fn [] (a*-search e (h-max (:actions e))))))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search ae))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (h-max (:actions ae))))))) (println (time (run-counted #(asplan-solution-pair-name (a*-search ae (let [h (h-max (:actions ae))] (fn [s] (- (h s) (unrealized-reward s)))))))))))

; (let [e (force (nth ipc2-logistics 3)) ] #_ (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(asplan-solution-pair-name (uniform-cost-search (make-asplan-env e)))))))


 ; (doseq [[alg sp]  [[make-asplan-env asplan-solution-pair-name] [angelic.search.action-set.asplan-broken/make-asplan-env angelic.search.action-set.asplan-broken/asplan-solution-pair-name]] ] (println (time (run-counted #(sp (uniform-cost-search (alg (make-random-infinite-taxi-sas2 3 3 3 3))))))))

; (-> (nth (vals (sas-sample-files 1)) 5) make-sas-problem-from-pddl unarize make-asplan-env interactive-search)

