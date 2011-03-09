(ns angelic.search.action-set.gasplan
  (:require [angelic.util :as util]
            [angelic.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]
            [angelic.hierarchy :as hierarchy]
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis])
  (:import [java.util HashMap]))


; Generalized version of ASPlan, to work in general domains.  
; For now, pretend analysis is free, just brute-force it. 

; Basic idea behind extension: 
;   Same as before, every action tries to change one var. 
;   This acts like a dummy precond link.
;   (i.e., can apply if var is free, or reserved for me.)

; Problems:
 ; (1) actions are split based on primary effect.
 ; (2) end up hallucinating huge pointless chains.
                                        ; (3) ways to assign parents multiples in general -- need to keep in control somehow.

;; Note: this fails completely, even on cyclic unary domains.
;; See, e.g., angelic.domains.unary-cyclic.clj.
;;Var z, vals 0, 1, initially 0.
;;a can transition along the line with no preconditions, except 0-->1 requires z = 1.
;;z can transition 0 --> 1 when a = -1.  

;; Seems to require either prediction or more interleaving, not handleable in this framework.

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
        [(free-var sas/goal-var-name) false]]))))

(def *add-count* (util/sref 0))

(defn make-add-action-action [{:keys [name precond-map effect-map reward] :as factored-primitive} target-var]
  (util/sref-set! *add-count* (inc (util/sref-get *add-count*)))
  (assert (contains? effect-map target-var))
  (let [eval (effect-map target-var)
        pval? (contains? precond-map target-var)]
    (env-util/make-factored-primitive
     [::AddAction name]
     (if pval? {(action-var target-var) nil, target-var (get precond-map target-var), (free-var target-var) false}
         {(action-var target-var) nil, (free-var target-var) false})
     {(action-var target-var) factored-primitive}
     reward)))

(defn make-set-parent-var-action [p-var c-var]
  (env-util/make-factored-primitive 
   [::SetParent p-var c-var] 
   {(free-var p-var) true} 
   {(free-var p-var) false (parent-var p-var c-var) true} 
   0))


; Try to make an action that greedily fires the action scheduled on effect-var,
; effectively representing a composition of set-parent and fire-action actions.
(defn make-greedy-fire-action [s effect-var]
  (let [{:keys [name precond-map effect-map reward] :as factored-primitive}
          (->> effect-var action-var (state/get-var s))
        precond-vars (keys (dissoc precond-map effect-var))
        effect-vars  (keys (dissoc effect-map effect-var))
        [free-pv unfree-pv] (util/separate #(state/get-var s (free-var %)) (concat precond-vars effect-vars))]
    (when (and (state/state-matches-map? s precond-map)
               (every? #(state/get-var s (parent-var % effect-var)) unfree-pv))
        (util/assert-is (every? #(nil? (state/get-var s (action-var %))) precond-vars) ); "%s" [name effect-var (println s)])
        (util/assert-is (every? #(nil? (state/get-var s (action-var %))) effect-vars))        
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


(defn current-child [s child-var-map p-var]
  (when-not (state/get-var s (free-var p-var))
    (util/find-first #(state/get-var s (parent-var p-var %))
      (child-var-map p-var))))

; Basic idea is to avoid bottom-up running into top-down in suboptimal way.
; This can happen if: a reserved precond with the right val has an action
(defn can-add-action? [s vars a target-var]
  (def *ba* [s a])
  (and (every? (fn [[pvar pval]] 
                 (not (and (state/get-var s (parent-var pvar target-var))
                           (state/get-var s (action-var pvar))
                           (= pval (state/get-var s pvar)))))
               (dissoc (:precond-map a) target-var))
       (every? #(or (not (vars %)) (not (and (state/get-var s (parent-var % target-var)) (state/get-var s (action-var %)))))
               (keys (dissoc (:effect-map a) target-var)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions fn, actual env ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplest way to express mechanics (in order of preference):

;  Schematics:
;  a* => A   goes to a* -> a   (greedy fire)
;  a => A    goes to  A => A   (bottom-up action)
;  a -> A    goes to  a => A   (bottom-up activate)
;  a => a => a goes to => A => a  (top-down action)          
;  a => a -> goes to a => a => (top-down activate)          

; Ideally, should prefer top-most top-down, bottom-most bottom-up, or something...

(defrecord GASPlanEnv [init actions-fn g-map]
  env/Env 
    (initial-state [this] init)
    (actions-fn    [this] actions-fn)
    (goal-fn       [this] #(when (state/state-matches-map? % g-map) (env/solution-and-reward %)))
  env/FactoredEnv
    (goal-map      [this] g-map))

(defn make-gasplan-env [sas-problem] 
  (def *add-count* (util/sref 0))
  (let [causal-graph  (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        relaxed-cg    (remove #(apply = %) (sas-analysis/relaxed-causal-graph sas-problem))
        vars          (graphs/ancestor-set relaxed-cg [sas/goal-var-name])
        causal-graph  (filter (fn [[v1 v2]] (and (vars v1) (vars v2))) causal-graph)
        av-map        (into {} (for [v vars] [v (graphs/ancestor-set causal-graph [v])]))
        child-var-map (util/map-vals #(map second %) (group-by first causal-graph))
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        simple-dtgs   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
        acyclic-succ-fn (partial possibly-acyclic-successors (HashMap.) simple-dtgs)]
    (GASPlanEnv. 
     (expand-initial-state (env/initial-state sas-problem) child-var-map (goal-action dtgs))
     (fn gasplan-actions [s]
      (when-not (deadlocked? s child-var-map []);)
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
              (for [n-val (acyclic-succ-fn pv p-val d-val), a (dtg n-val)
                    :when (can-add-action? s vars a pv)] ;->ASPLAN2
                (make-add-action-action a pv)))

          ;; Inactive bottom-up var -- needs to be assigned.  
          (util/find-first #(state/get-var s (free-var %)) (map first aa-parent-edges))
            (do (println "??????????!!") (activation-actions child-var-map x))
;; tODO: put below back, needed for correctness!
          ;; Active top-down var -- add actions
;            (util/find-first #(and (not (state/get-var s (free-var %)))
;                                 (not (state/get-var s (action-var (current-child s child-var-map %))))) ;->ASPLAN1
;                           (map second na-tuples))  
;            (do ;(println "A!" x (state/get-var s x) )
;             (for [as (vals (util/safe-get-in dtgs [x (state/get-var s x)])), a as]
;               (make-add-action-action a x)))

          ;; Inactive top-down var -- activate it
;          (util/find-first #(state/get-var s (free-var %)) (map second na-tuples))
;            (do ;(println "I!")
;             (activation-actions child-var-map x)))));)
            ))))
     (env/goal-map sas-problem))))

(defn gasplan-solution-name [sol]
  (map second (filter #(= (first %) ::GreedyFire) sol)))

(defn gasplan-solution-pair-name [[sol rew]]
  [(gasplan-solution-name sol) rew])

;; TODO: put into asplan:
 ; Guard on adding top-down action into spot where bottom-up would put it if it wanted it...



;(let [e (make-sas-problem-from-pddl (angelic.taxi/write-taxi-strips (angelic.taxi/make-random-taxi-env 3 3 3))) ]  (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(angelic.gasplan/gasplan-solution-pair-name (uniform-cost-search (angelic.gasplan/make-gasplan-env e)))))))

;(doseq [ [k v] (sas-sample-files 1) :let [e (make-sas-problem-from-pddl v)]  ] (println "\n\n" k ) (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(angelic.gasplan/gasplan-solution-pair-name (uniform-cost-search (angelic.gasplan/make-gasplan-env e)))))))