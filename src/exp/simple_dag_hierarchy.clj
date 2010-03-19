(ns exp.simple-dag-hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: in purely static analysis, either cannot prune source vals, or must 
;; split HLAs.  Here, this amounts to, more or less, just removing outgoing arcs from goal.
;; We can just do this implicitly, and forget about real acyclic stuff in this version.
; TODO: (could do better, e.g., for line DTGs)
; In fact, this makes thngs *ugly* for even simple taxi


;; I.e, when searching backwards from goal, source is necessary predecessor of target.


(declare make-action-hla)

(deftype Simple-DAG-Hierarchy 
  [sas-problem 
   predecessor-var-set
   ancestor-var-set
   var-levels
   dtg-to       ; fn from var & dst-val to map from cur-val to map from nxt-val to actions
   cycle-to     ; from from var & dst-val to map from cur-val to bool, if can cycle from cur-val
   greedy-optimization?])

(defn make-simple-dag-hierarchy [sas-problem]
  (let [causal-graph (remove #(apply = %) (sas-analysis/standard-causal-graph sas-problem))
        pred-var-set (util/map-vals (comp set #(map first %))
                                    (util/unsorted-group-by second causal-graph)) 
        dtgs         (sas-analysis/domain-transition-graphs sas-problem)
        sr-dtg       (memoize (fn [var] (for [[pv em] (dtgs var), nv (keys em)] [nv pv])))
        dtg-to       (memoize (fn [var to-val] ;; Edges s.t. all paths from nv to goal include pv
                                ;(println "Computing dtg for" var to-val)
                                 (let [np (graphs/compute-reachable-nodes-and-necessary-predecessors
                                             (sr-dtg var) to-val)]
                                     (util/map-map 
                                      (fn [[pv emap]]
                                        [pv
                                         (util/filter-map 
                                          (fn [[nv]] (not (contains? (get np nv) pv)))
                                          emap)])
                                      (dtgs var)))))]

    (assert (graphs/dag? causal-graph))
    (assert (sas-analysis/homogenous? sas-problem))    
  
    (hierarchy/SimpleHierarchicalEnv sas-problem 
      [(make-action-hla 
        (Simple-DAG-Hierarchy
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
           (println "computing cycle-to for" var dst-val)
           (let [dtg (dtg-to var dst-val)]
             (reduce (fn [m next-vars]
                       (if (> (count next-vars) 1)
                           (reduce #(assoc %1 %2 true) m next-vars)
                         (let [v (util/safe-singleton next-vars)]
                           (assoc m v (some m (keys (get dtg v)))))))
                     {} 
                     (reverse (vals (second (graphs/scc-graph 
                                             (for [[pval emap] dtg, eval (keys emap)] 
                                               [pval eval]))))))))
         false)
        (-> dtgs
            (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
            util/safe-singleton))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#_ (defprotocol SDH-Action
  (precond-var-set [a])
  (effect-sets     [a])
  (pre-ref-pairs   [a])
  (compile-hla     [a retain-type-set])
  (extend-hla!     [a init-sets par-effect-sets])
  (hla-type        [a]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype SDH-Precond-HLA  [hierarchy name var dst-val dtg precond-var-set] :as this
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

(defn- make-precond-hla [hierarchy var dst-val]
  (SDH-Precond-HLA hierarchy [:!P var dst-val] var dst-val 
                   ((:dtg-to           hierarchy) var dst-val)
                   ((:ancestor-var-set hierarchy) var)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precond Set HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is where all the interleaving magic happens

(deftype SDH-Precond-Set-HLA  [hierarchy name var dst-val dtg precond-var-set] :as this
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

(defn- make-precond-set-hla [hierarchy var dst-val]
  (SDH-Precond-Set-HLA hierarchy [:!P var dst-val] var dst-val 
                   ((:dtg-to           hierarchy) var dst-val)
                   ((:ancestor-var-set hierarchy) var)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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
                    (make-precond-set-hla hierarchy (select-keys pc-map pc-batch)))
              (let [pc (util/safe-singleton pc-batch)]
                (make-precond-hla hierarchy pc (get pc-map pc))))))
        [action])])
    (cycle-level-           [s] nil))

(defn- make-action-hla [hierarchy action]
  (let [effect-var (key (util/safe-singleton (:effect-map action)))]
    (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action effect-var
                    ((:ancestor-var-set hierarchy) effect-var))))

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