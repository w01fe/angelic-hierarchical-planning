(ns dag-cpo
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]]))

;; Cached partial order planner
;; Implements search with *waits*, no explicit hierarchy

;; Basic process: depth-first search,
;; Have state + tree-in-progress
;; Ops are: expand causal commitment edge, connect
;; open precondition to first producer (connected to init) or blacklist.  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Protocols      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype Blocked-Refinement [state reward cc-map blacklist-map rest-tree])
(deftype Completed-Refinement [state reward blacklist-map])
 ; blacklist-map will always be better than what came in


(defprotocol CPO-Node
  (can-progress? [n s blacklist-map ancestor-vars])
  (refinements-  [n s blacklist-map ancestor-vars])
  )


(deftype CPO-Problem
  [sas-problem 
   predecessor-var-set
   ancestor-var-set
   var-levels
   interfering-set ; fn from var to set of vars: descendents of ancestors but not descendents. 
   dtg-to       ; fn from var & dst-val to map from cur-val to map from nxt-val to actions
   cycle-to     ; from from var & dst-val to map from cur-val to bool, if can cycle from cur-val
   greedy-optimization?])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn refinements [a s cc-map blacklist-map ancestor-vars])


; Source will usually be nil, meaning connection to initial state. ? 
;; For now, punt, and just fail if we hit this condition?  Wont' be present in many domains.
(deftype CPO-CC [problem var src-val dst-val source]  
  CPO-Node
    (refinements- [s]
      ; if all normal, generate & refine first action
      ;;; What if I have a src/ blacklist ? 
      ...
      ))
;; How do we do cycle stuff?  Hybrid?  ...

(deftype CPO-OP [problem var dst-val]
  CPO-Node
    (can-progress? [s blacklist-map ancestor-vars]
      (or (empty? blacklist-map)
          (if-let [bp (blacklist-map var)]
              (not= (first ancestor-vars) bp)
            (... ? ))))
    (refinements- [s blacklist-map ancestor-vars]
      (when-not (is-blocked? ...)
        (util/cons-when
         (when can-block? (Blocked-Refinement. ...))
         (refinements (CPO-CC. ...))))))

(deftype CPO-Action [problem action preconditions] :as this
  CPO-Node
    (refinements- [s blacklist-map ancestor-vars]
      (let [[bp rp] (split-with #(blocked? n s blacklist-map ancestor-vars) preconditions)]
        (if-let [[fp & mp] (seq rp)] 
            (for [ref (refinements fp ...)]
              (case (type ref) 
                    ::BlockedRefinement
                      (let [{:keys [state reward cc-map blacklist-map rest-tree]} ref]
                        (refinements (CPO-Action. problem action (concat bp [rest-tree] mp))
                                     state reward ???? blacklist-map ancestor-vars))
                    ::CompletedRefinement
                      (let [{:keys [state reward blacklist-map]} ref]
                        (refinements (CPO-Action. problem action (concat bp mp))
                                     state reward blacklist-map ancestor-vars))))
          (Blocked-...) ...)
        )
                 ))
; When blocked, be sure to include all preconds (incl. finished) in ret.
;; can-progress/blocked? doesn't make sense, b/c we need info out of these for our return.
;; Seems mutable nodes with caching are way to go instead. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Driver        ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn solve-cpo
  ([sas-problem] (make-cpo-problem sas-problem true))
  ([sas-problem greedy?]
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
  
       (hierarchy/SimpleHierarchicalEnv 
        sas-problem 
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
            (memoize
             (fn interfering-set [var] 
               (clojure.set/difference 
                (graphs/descendant-set causal-graph (graphs/ancestor-set causal-graph [var]))
                (graphs/descendant-set causal-graph [var]))))
            dtg-to
            (util/memoized-fn cycle-to [var dst-val]
              (println "computing cycle-to for" var dst-val)
              (let [dtg (dtg-to var dst-val)]
                (reduce (fn [m next-vars]
                          (if (> (count next-vars) 1)
                            (reduce #(assoc %1 %2 true) m next-vars)
                            (let [v (util/safe-singleton next-vars)]
                              (assoc m v (some m (keys (get dtg v)))))))
                        {} (reverse (vals (second (graphs/scc-graph 
                                                   (for [[pval emap] dtg, eval (keys emap)] 
                                                     [pval eval]))))))))
            greedy?)
           (-> dtgs
               (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
               util/safe-singleton))]))))