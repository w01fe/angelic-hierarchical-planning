(ns exp.simple-tree-hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: in purely static analysis, either cannot prune source vals, or must 
;; split HLAs.  Here, this amounts to, more or less, just removing outgoing arcs from goal.
;; We can just do this implicitly, and forget about real acyclic stuff in this version.
; TODO: (could do better, e.g., for line DTGs)



(declare make-action-hla)

(deftype Simple-Tree-Hierarchy 
  [sas-problem 
   predecessor-var-set
   ancestor-var-set
   var-levels
   dtg-to       ; fn from var & dst-val to map from cur-val to map from nxt-val to actions
   cycle-to     ; from from var & dst-val to map from cur-val to bool, if can cycle from cur-val
   greedy-optimization?])

(defn make-simple-tree-hierarchy [sas-problem]
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        pred-var-set (util/map-vals (comp set #(map first %))
                                    (util/unsorted-group-by second causal-graph)) 
        dtgs         (sas-analysis/domain-transition-graphs sas-problem)
        dtg-to       (fn [var dst-val] (util/safe-get dtgs var))]

    (assert (graphs/inverted-tree-reducible? causal-graph))
    (assert (sas-analysis/homogenous? sas-problem))    
  
    (hierarchy/SimpleHierarchicalEnv sas-problem 
      [(make-action-hla 
        (Simple-Tree-Hierarchy
         sas-problem
         pred-var-set
         (util/memoized-fn ancestor-var-set [var]
           (conj (->> (pred-var-set var)
                      (map ancestor-var-set)
                      (apply clojure.set/union))
                 var))
         (graphs/topological-sort-indices causal-graph)
         dtg-to
         (util/memoized-fn cycle-to [var dst-val]
           (let [dtg (dtg-to var dst-val)
                 tsi (graphs/topological-sort-indices
                      (for [[pval emap] dtg, eval (keys emap)
                            :when (not (= pval dst-val))] 
                        [pval eval]))]
             (reduce (fn [m next-vars]
                       (if (> (count next-vars) 1)
                           (reduce #(assoc %1 %2 true) m next-vars)
                         (let [v (util/safe-singleton next-vars)]
                           (assoc m v (some m (keys (get dtg v)))))))
                     {} (reverse (map #(map key %) (vals (util/group-by val tsi)))))))
         false)
        (-> dtgs
            (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
            util/safe-singleton))])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype STH-Precond-HLA  [hierarchy name var dst-val dtg precond-var-set cycle-level] :as this
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
            [(make-action-hla action) this]))))
    (cycle-level-           [s] cycle-level))

(defn- make-precond-hla [hierarchy var dst-val]
  (STH-Precond-HLA hierarchy [:!PRECOND var dst-val] var dst-val 
                   ((:dtg-to            hierarchy) var dst-val)
                   ((:ancestor-var-set hierarchy) var)
                   (when ((:cycle-to hierarchy) var dst-val)
                     ((:var-levels hierarchy) var))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype STH-Action-HLA [hierarchy name action precond-hlas precond-var-set]
  env/Action
    (action-name     [] name)
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] precond-var-set)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] (concat precond-hlas [action]))
    (cycle-level-           [s] nil))

(defn- make-action-hla [hierarchy action]
  (let [effect-var (key (util/safe-singleton (:effect-map action)))]
    (STH-Action-HLA hierarchy [:!A (env/action-name action)] action 
                    (for [[var val] (sort-by (comp - (:var-levels hierarchy) key) 
                                             (:precond-map action))
                          :when (not (= var effect-var))] 
                      (make-precond-hla hierarchy var val))
                    ((:ancestor-var-set hierarchy) effect-var))))


