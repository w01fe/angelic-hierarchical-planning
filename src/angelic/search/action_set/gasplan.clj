(ns angelic.search.action-set.gasplan2
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


;; Generalized version of asplan for non-unary domains.

;; no greedy for side-effects,
;; no directed unless all side effects scheduled,
;; TODO greedy for 'nice' effects

;; Need to identify possible actions, children given commitments.
;; I.e., for resources no actions should e allowed, that propagates.
;; 


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

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive} evar]
  (util/sref-set! *add-count* (inc (util/sref-get *add-count*)))
  (assert (contains? effect-map evar))
  (env-util/make-factored-primitive
   [::AddAction name evar]
   {(action-var evar) nil, evar (util/safe-get precond-map evar)}
   {(action-var evar) factored-primitive}
   reward))

(defn make-set-parent-var-action [p-var c-var]
  (env-util/make-factored-primitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


;; TODO: free increases.
(defn make-greedy-fire-action [s evar]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> evar action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map evar))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) precond-vars)]
    (assert (every? #(contains? #{nil :frozen} (state/get-var s (action-var %))) precond-vars))
    (doseq [p precond-vars]
      (when (contains? effect-map p)
        (assert (state/get-var s (parent-var p evar)))))    

    (env-util/make-factored-primitive
     [::Fire name]
     (into precond-map 
           (concat [[(action-var evar) factored-primitive]]
                   (for [v free-pv]   [(free-var v)         true])
                   (for [v unfree-pv] [(parent-var v evar)  true])
                   (for [v precond-vars] [(action-var v) (state/get-var s (action-var v))])))           
     (into effect-map 
           (concat [[(action-var evar) nil]]
                   (for [v unfree-pv] [(free-var v)         true])
                   (for [v unfree-pv] [(parent-var v evar)  false])
                   (for [v precond-vars] [(action-var v) nil])))
      0)))




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
  (assert (= rule :greedy))
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
                                                  (or (not right-val?)
                                                      (and (contains? (:effect-map a) p) (not (= (state/get-var s (action-var p)) :frozen))))
                                                    [p v]))))))))))


;#_(when-not (some #(let [c (current-child s child-map %)]
;(not (or (= p-child nil) (= p-child v))))
;(keys (dissoc (:precond-map a) v)))
;[p v])  ;; TODO: put back?


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

(defn scheduled-side-effector? [s v side]
  (when-let [a (state/get-var s (action-var side))]
    (and (not (= a :frozen))
         (contains? (:effect-map a) v))))


;; also need to worry about "root" here
(defn activation-actions  "Return a list of all activation actions for var v"
  [s v child-map prevail-map]
  (let [prevail-set (get prevail-map v #{})]
    (for [c (child-map v)
          :when (or (prevail-set c) (scheduled-side-effector? s v c))]
      (make-set-parent-var-action v c))))

(defn add-actions [s v dtgs]
  (cons (make-freeze-var-action v)
        (for [as (vals (get-in dtgs [v (state/get-var s v)])), a as]
          (make-add-action-action a v))))

(defn conflicted-effects? [s v a]
  (some #(scheduled-side-effector? s v %)
        (keys (dissoc (:effect-map a) v))))


;; Here, need to worry about side effects.
;; If there are cycles that do not effect the reserving action
(defn add-directed-actions [s v dtgs cvm acyclic-succ-fn effect-cluster-map]
  (let [c-val (state/get-var s v)
        dtg   (get-in dtgs [v c-val])
        child (current-child s cvm v)
        d-val (-> (state/get-var s (action-var child)) :precond-map (get v))]
    (if d-val
      (if (every? (fn [side-var] (scheduled-side-effector? s v side-var)) (disj (effect-cluster-map v) v))      
        (if (= c-val d-val)
          [(make-freeze-var-action v)]
          (for [n-val (acyclic-succ-fn v c-val d-val), a (dtg n-val)
                :when (not (conflicted-effects? s v a))]
            (make-add-action-action a v)))
        (concat
         (when (= c-val d-val) [(make-freeze-var-action v)])
         (for [[n-val actions] dtg, action actions ;; TODO??
               :when (not (conflicted-effects? s v action))]
           (make-add-action-action action v))))      
      ;; This should only arise in cyclic domains -- TODO: remove?
      (do (assert nil) (add-actions s v dtgs)))))

; (some (fn [sev] (= action (state/get-var s (action-var sev)))) (keys (dissoc (:effect-map action) v)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ASPlanEnv [base-sas-env init actions-fn g-map ]
  env/Env 
    (initial-state [e] init)
    (actions-fn    [e] actions-fn)
    (goal-fn       [e] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [e] g-map))

;; TODO: should be pruning as soon as we reserve cap.


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
           tsi           (graphs/df-topological-sort-indices prevail-cg) ;; way worse.
           prevail-cvm   (util/map-vals set (graphs/edge-list->outgoing-map prevail-cg))
           effect-cluster-map (into {} (for [cluster (sas-analysis/effect-clusters sas-problem), v cluster] [v cluster]))
           dtgs          (sas-analysis/domain-transition-graphs sas-problem)
           simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
           acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
;       (assert (graphs/dag? causal-graph))    
 ;       (assert (sas-analysis/unary? sas-problem))
       (println tsi)
       (doseq [a (:actions sas-problem)]
         (when-not (every? (partial contains? (:precond-map a)) (keys (:effect-map a)))
           (println (:name a) (apply dissoc (:effect-map a) (keys (:precond-map a))))))       
       (doseq [a (:actions sas-problem)]
         (assert (every? (partial contains? (:precond-map a)) (keys (:effect-map a)))))

       
       (ASPlanEnv.
        sas-problem
        (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))

        (fn asplan-actions [s]
;          (println "\n" (:act-seq (meta s))) (Thread/sleep 100)
          (when-let [sources (and (or (not dead-vars?) (not (uses-dead-vars? s av-map child-var-map []))) 
                                  (seq (source-vars s child-var-map deadlock? components? edge-rule)))]
            (let [sources-by-type (group-by #(source-var-type s child-var-map %) sources)]
;              (println sources-by-type)
              (util/cond-let [sources]
                (seq (sources-by-type :fire))
                [(make-greedy-fire-action s (first sources))]

                (seq (sources-by-type :bottom-up-action))
                (if directed?
                  (add-directed-actions s (apply min-key tsi sources) dtgs child-var-map acyclic-succ-fn effect-cluster-map)
                  (add-actions s (apply min-key tsi sources) dtgs))               
                     
                (seq (sources-by-type :bottom-up-activate))
                (activation-actions s (apply max-key tsi sources) child-var-map prevail-cvm) ;; TODO: smarter sort!
                
                (seq (sources-by-type :top-down-activate))
                (do (println "I!") (activation-actions s (first sources) child-var-map prevail-cvm))
                
                (seq (sources-by-type :top-down-action))
                (do (println "A!") (add-actions s (first sources) dtgs))
                
                :else (assert "Unknown source type!")))))
        (env/goal-map sas-problem)))))



(defn asplan-solution-name [sol]
  (map second (filter #(= (first %) ::Fire) sol)))

(defn asplan-solution-pair-name [[sol rew]]
  [(asplan-solution-name sol) rew])





;; (use 'angelic.env 'angelic.hierarchy 'angelic.search.textbook 'angelic.domains.taxi-infinite 'angelic.search.action-set.asplan  'angelic.domains.sas-problems 'angelic.sas 'angelic.sas.analysis 'angelic.util 'angelic.sas.hm-heuristic)

;; (require '[angelic.search.action-set.gasplan :as gap])

;; (let [e (force (nth ipc2-logistics 5)) ]  (println (time (run-counted #(ap/asplan-solution-pair-name (uniform-cost-search (ap/make-asplan-env e ))))))  (println (time (run-counted #(ap2/asplan-solution-pair-name (uniform-cost-search (ap2/make-asplan-env e )))))) (println (time (run-counted #(gap/asplan-solution-pair-name (uniform-cost-search (gap/make-asplan-env e )))))))


