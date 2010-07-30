(ns dag-cpo
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [w01fe [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]]))

;; Cached partial order planner
;; Implements search with *waits*, no explicit hierarchy

;; Basic process: depth-first search,
;; Have state + tree-in-progress
;; Ops are: expand causal commitment edge, connect
;; open precondition to first producer (connected to init) or blacklist.  

; Question: how do we keep track of commitment ordering?
; Can just keep a list of nodes?  

; Really, along with tree, just need a map from vars to in-progres things?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Protocols      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; var-cc-map is map from vars to list of cc-nodes left.
;; rest-tree is nil iff completed, else blocked.  
(deftype Refinement [state reward blacklist-map var-cc-nodes rest-tree])

; Ancestor-chain does not include currently considered var.
(defprotocol CPO-Node
  (refinements-  [n state blacklist-map var-cc-nodes ancestor-chain])
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

(defn refinements [a s  blacklist-map ancestor-chain])

;; How do we know if its done? 
; Source will usually be nil, meaning connection to initial state. ? 
;; For now, punt, and just fail if we hit this condition?  Wont' be present in many domains.

(deftype CPO-CC [problem var src-val dst-val queue]  
  CPO-Node
    (refinements- [state blacklist-map var-cc-nodes ancestor-chain]
                  
      ; if all normal, generate & refine first action
      ;;; What if I have a src/ blacklist ? 
      ;; what if i already have a first action.
      ;; Actions will need to do the same
                 ; --> separate sequence + op concepts? 
      ...
      ))

(defn make-cc-node [op-node state var-cc-nodes]
  (let [{:keys [problem var dst-val]} op-node]
    (CPO-CC problem var (if-let [ccn (var-cc-nodes var)] (:dst-val (last ccn)) (env/get-var state var)) dst-val nil)))

;; How do we do cycle stuff?  Hybrid?  ...


;; Are there alternatives to access the virst var in this chain?
; If no var passed, look at all descenents in the chain.
; If var passed, we look only from that var (possibly on the chain)
(defn alternatives? 
  ([ancestor-chain]
     ...
     )
  ([ancestor-chain from-var]
     ...
     ))

;; If no blacklists, good to do.
;  If blacklists: only good to go if I'm not blacklisted, and I my children can make progress on a blacklist.
(defn blocked? [var op-node blacklist-map]

  )

(deftype CPO-OP [problem var dst-val parent-var] :as this
  CPO-Node
    (refinements- [state blacklist-map var-cc-nodes ancestor-chain]
      (if (blocked? this blacklist-map)
          (Refinement state 0 blacklist-map var-cc-nodes this)
        (util/cons-when
         (when (alternatives? (cons var ancestor-chain)) 
           (Refinement state 0 (assoc blacklist-map var (cons parent-var (blacklist-map var))) var-cc-nodes this))
         (let [cc (make-cc-node problem var dst-val state var-cc-nodes)]
           (refinements cc state (dissoc blacklist-map var) (update-in var-cc-nodes [var] concat [cc]) ancestor-chain))))))

;; Parse action into main-effect, ignore it.
;; Be sure to add var to ancestor-chain here.
(deftype CPO-Action [problem action preconditions] :as this
  CPO-Node
    (refinements- [s blacklist-map var-cc-nodes ancestor-chain]
      (let [[bp rp] (split-with #(blocked? n s blacklist-map ancestor-chain) preconditions)]
        (if-let [[fp & mp] (seq rp)] 
            (for [ref (refinements fp ...)]
              (case (type ref) 
                    ::BlockedRefinement
                      (let [{:keys [state reward cc-map blacklist-map rest-tree]} ref]
                        (refinements (CPO-Action. problem action (concat bp [rest-tree] mp))
                                     state reward ???? blacklist-map ancestor-chain))
                    ::CompletedRefinement
                      (let [{:keys [state reward blacklist-map]} ref]
                        (refinements (CPO-Action. problem action (concat bp mp))
                                     state reward blacklist-map ancestor-chain))))
          (Blocked-...) ...)
        )
                 ))
; When blocked, be sure to include all preconds (incl. finished) in ret.
;; can-progress/blocked? doesn't make sense, b/c we need info out of these for our return.
;; Seems mutable nodes with caching are way to go instead. 
;; Except, how do we branch? 


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