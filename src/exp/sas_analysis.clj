(ns exp.sas-analysis
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util [queues :as queues] [graphviz :as gv] [graphs :as graphs]]
            [exp [sas :as sas] [env :as env]])
  (:import [java.util HashMap HashSet]))


;;;;;;;;;;;;;;;;;;;;;;;;;; Causal graphs, DTGS, etc.          ;;;;;;;;;;;;;;;;;;;;;;;;


(defn domain-transition-graphs 
  "Return a map from var to map from val to map from next-val to seq of actions
   causing this transition."
  [vars actions]
  (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
          (for [a actions
                [evar eval] (:effect-map a)
                pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                :when       (not (= eval pval))]
            [[evar pval eval] a])))

(defn show-dtgs [sas-problem]
  (gv/graphviz-el   
   (for [[vn dtg] (domain-transition-graphs (:vars sas-problem) (:actions sas-problem))
         [s d-map] dtg
         [d _]     d-map]
     [(cons vn s) (cons vn d)])))

(defn reverse-domain-transition-graphs
  "Return a map from var to map from val to map from prev-val to seq of actions
   causing this transition."
  [vars actions]  
  (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
          (for [a actions
                [evar eval] (:effect-map a)
                pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                :when       (not (= eval pval))]
            [[evar eval pval] a])))


(defn standard-causal-graph 
  "Return an edge list for a standard causal graph of the problem."
  [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (for [action actions
           precondition (concat (:precond-map action) (:effect-map action))
           effect       (:effect-map action)]
       [(first precondition) (first effect)]))))

(defn relaxed-causal-graph
  "Return an edge list for a standard causal graph of the problem, which does not
   include edges bewteen effects of the same action."
  [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (concat (for [vn (keys vars)] [vn vn])
             (for [action actions
                   precondition (:precond-map action)
                   effect       (:effect-map action)]
               [(first precondition) (first effect)])))))

(defn show-causal-graph
  "Display the relaxed causal graph."
  [sas-problem]
  (gv/graphviz-el (relaxed-causal-graph sas-problem)))

(defn show-causal-graph-sccs
  "Display the strongly connected components of the relaxed causal graph."
  [sas-problem]
  (apply gv/graphviz-el (graphs/scc-graph (relaxed-causal-graph sas-problem))))

;; This is analogous to delete-list relaxation...
(defn state-action-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (apply concat 
           (for [a actions]
             (concat (for [[var val] (:precond-map a)] [[var val] (:name a)])
                     (for [[var val] (:effect-map  a)] [(:name a) [var val]]))))))

(defn show-state-action-graph 
  "Display a graph showing the preconditions and effects of all actions in the domain."
  [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (gv/graphviz-el 
     (apply concat 
            (for [a actions]
              (concat (for [[var val] (:precond-map a)] [val (:name a)])
                      (for [[var val] (:effect-map  a)] [(:name a) val]))))
     (into (util/identity-map (apply concat (map :vals (vals vars))))
           (for [a actions]
             [(:name a) {:label (util/double-quote (:name a)) :shape "box"}])))))


(defn show-strips-causal-graph 
  "Display the causal graph of a STRIPS version of the SAS problem."
  [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (gv/graphviz-el
     (distinct
      (remove #(apply = %)
       (apply concat 
        (for [a actions]
          (for [[pvar pval] (:precond-map a),
                [evar eval] (concat (:effect-map a) (select-keys (:precond-map a) (keys (:effect-map a))))]
            [pval eval]))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;; Simple, non-mutex forward analysis ;;;;;;;;;;;;;;;;;;;;;;;;

(defn forward-analyze 
  "Take an SAS-problem, and return [untested-vals unset-vals unreachable-actions]"
  [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        untested-vals               (HashSet.)
        unset-vals                  (HashSet.)
        action-precond-counts       (HashMap.)
        actions-by-precond          (HashMap.)
        stack                       (queues/make-stack-pq)]
    (doseq [var (vals (dissoc vars sas/goal-var-name)), val (:vals var)] 
      (.add untested-vals [(:name var) val])
      (.add unset-vals [(:name var) val]))
    (doseq [[var val] init] (.remove unset-vals [var val]))
    (doseq [a actions]
      (.put action-precond-counts a (count (:precond-map a)))
      (when (empty? (:precond-map a)) (queues/pq-add! stack a 0))
      (doseq [[var val] (:effect-map a)] (.remove unset-vals [var val]))
      (doseq [[var val] (:precond-map a)]
        (.remove untested-vals [var val])
        (.put actions-by-precond [var val] (cons a (.get actions-by-precond [var val])))))
    (queues/pq-add! stack (env/FactoredPrimitive [:init] {} init 0) 0)
    (while (not (queues/pq-empty? stack))
        (doseq [[var val] (:effect-map (queues/pq-remove-min! stack))
                a (.remove actions-by-precond [var val])]
          (let [c (dec (.remove action-precond-counts a))]
            (if (> c 0)
                (.put action-precond-counts a c)
              (queues/pq-add! stack a 0)))))
;    (println (util/map-vals count (util/group-by first  untested-vals)))
    (println (count unset-vals) (count untested-vals) (count actions-by-precond) (count action-precond-counts))
    [untested-vals (concat unset-vals (keys actions-by-precond)) (keys action-precond-counts)]))



;;;;;;;;;;;;;;;;;;;;;;;;;; Static analysis for finding equivalent vals ;;;;;;;;;;;;;;;;;;;;;;;;

;; Do static look at actions and find equivalent vals
 ; These are: ones that are always set at the same time, AND
 ; all ways of unsetting them unset both.  Slow for now.
(defn canonical-vv [pair] (sort-by first pair))

(defn find-static-equivalence-pairs [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        actions                     (cons (env/FactoredPrimitive [:init] {} init 0) actions)
        extended-dtgs               (domain-transition-graphs vars actions)
        extended-rdtgs              (reverse-domain-transition-graphs vars actions)]
    (filter
     (fn [[[var1 val1] [var2 val2]]]
       (when (< (.compareTo #^Comparable var1 #^Comparable var2) 0)
         (every? (fn [[var val other-var other-val]]
                   (every? (fn [a] (not (= (get (:effect-map a) other-var other-val) other-val)))
                           (apply concat (vals ((extended-dtgs var) val)))))
                 [[var1 val1 var2 val2] [var2 val2 var1 val1]])))
     (apply concat
            (for [[vn extended-rdtg] extended-rdtgs
                  [val incoming-map] extended-rdtg]
              (disj (apply clojure.set/intersection (map #(set (map (juxt (constantly [vn val]) vec) (:effect-map %))) 
                                                         (apply concat (vals incoming-map)))) 
                    [vn val]))))))

(defn find-static-equivalence-sets [sas-problem]
  (let [pairs           (find-static-equivalence-pairs sas-problem)
        symmetric-pairs (apply concat (for [[x y] pairs] [[x y] [y x]]))]
    (loop [remaining-map (util/map-vals #(set (map second %)) (util/group-by first symmetric-pairs)), results nil]
      (if (empty? remaining-map) results
        (let [[fk fs] (first remaining-map)]
          (let [all 
                (loop [cur (conj fs fk)]
                  (let [nxt (apply clojure.set/union (map (partial get remaining-map) cur))]
                    (if (= cur nxt) cur (recur nxt))))]
            (recur (apply dissoc remaining-map all) (cons all results))))))))

;;Return a mapping from vars to val-remappings
; In some weird cases, right set of vars to eliminate may be non-obvious.
;;In more cases, right val to choose may be non-obvious.
;; Algorithm: find redundant vars (easy), pick deletes 
;; TODO: if two vars have same domain size, and n-1 proven equivs, are equiv.
(defn find-redundant-vars 
  ([sas-problem] (find-redundant-vars sas-problem (find-static-equivalence-sets sas-problem)))
  ([sas-problem equiv-sets]
     (let [vars           (:vars sas-problem)
           redundant-vars (set (map first (filter (fn [[x xxx]] (let [vc (count (:vals (vars x))) rc (count xxx)]
                                                                  (assert (<= rc vc)) 
                                                                  (or (= vc rc) )))
                                                  (util/group-by first (apply concat equiv-sets)))))
           val-equivs     (reduce (fn [m [ks v]] (assoc-in m ks v))
                                  {}
                                  (for [equiv-set equiv-sets, [var val :as p] equiv-set
                                        :when (contains? redundant-vars var)]
                                    [[var val] (disj equiv-set p)]))
           var-equivs     (util/map-vals 
                           (fn [equiv-map] (apply clojure.set/intersection (map #(set (map first %)) (vals equiv-map))))
                           val-equivs)
           equiv-graph    (for [[k vs] var-equivs, v vs] [k v])
           [scc-graph scc-nodes] (graphs/scc-graph equiv-graph)]
       (assert (every? (partial apply =) scc-graph))
       (println (count redundant-vars) "redundant vars in" (count scc-nodes) "equivalence classes;"
                "can remove" (- (count redundant-vars) (count scc-nodes))) 
       (map set (vals scc-nodes)))))

(defn equivalence-info [sas-problem]
  (let [equiv-sets     (find-static-equivalence-sets sas-problem)
        var-equiv-sets (find-redundant-vars sas-problem equiv-sets)
        all-equiv-vars (apply clojure.set/union var-equiv-sets)
        rem-equiv-sets (remove empty?
                        (for [es equiv-sets]
                          (if (some all-equiv-vars (map first es))
                            (let [rem (set (remove #(all-equiv-vars (first %)) es))]
                              (when (seq rem) (conj rem [:es :???])))
                            es)))]
    (println "Remaining equivalences: " (count rem-equiv-sets))
    rem-equiv-sets))










;;;;;;;;;;;;;;;;;;;;;;;;;; Unfinished attempt to do forward mutex reasoning ;;;;;;;;;;;;;;;;;;;;;;;;


; (doseq [ [n f] (sas-sample-files 1)] (println "\n\n"  n) (equivalence-info (make-sas-problem-from-pddl f)))


 ; make implicit persist actions.  
;; Run planning graph, with mutexes
 ; state layer is pair [allowed-vv-set allowed-vv-pair-set]
 ; action layer is [allowed-actions mutex-actions]
;; Can do similar queue-based scheme:
 ; New action available can add to vv-set, allowed-vv-pair-set in obvious way.
  ; (note implicit mutex with implicit persist actions for vxv in preconds,
  ;  all vars in effects)
 ; New val available can add actions, 

;; State to action layer:
; actions are permanent mutex if 

(comment 
  (defn canonical-vv [pair] (sort-by first pair))
  (defn canonical-aa [pair] (sort-by :name pair))

  (defn next-action-layer [[new-vals new-val-pairs] ....]
    ;; Find new actions - indexed by # of preconds + precond pairs left to go.
  
    ;; Find new action pairs - can be 
                                        ; (1) 
  
    (.addAll live-vals new-vals)
    (.addAll live-val-pairs new-val-pairs)
    )

;; Do simple forward analysis, and return [equiv-vals mutex-vals]
  (defn find-mutexes [sas-problem]
    (let [{:keys [vars actions init]} sas-problem
          vars                        (apply sorted-map (apply concat vars))
          persist-actions             (for [[vn var] vars, val (:vals var)] (SAS-Action [:persist vn val] {vn val} {vn val} 0))
          live-vals                   (HashSet.)
          live-val-pairs              (HashSet.)
          live-actions                (HashSet.)
          live-action-pairs           (HashSet.)]

      ;; Fill in initial live-action-pairs ? 
      (loop [[new-vals new-val-pairs] [(map vec init)  (distinct (map vec (for [v1 init, v2 init] (canonical-vv [v1 v2]))))]]
        (if (empty? new-val-pairs) [(count live-vals) (count live-val-pairs) (count live-actions) (count live-action-pairs)]
            (recur (next-state-layer
                    (next-action-layer
                     [new-vals new-val-pairs]
                     ...
                     )
                    ...)))))))


;;;;;;;;;;;;;;;;;;;;;; Unfinished attempt to do backwards relevance analysis ;;;;;;;;;;;;;;;;;;;;;;


;; Backward simplification: 
;; Can remove anything provably not on a shortest path to goal.  
;; Basically, this comes down to finding irrelevant "spokes" in DTGs and removing them. 
;; Should also provide things like: never pick up a passenger you've already put down ?
;; Ideally, at the top-level would prune everything based on actual shortest paths...

;; SO, do pruning as we walk up.  Do need to precompute causal graph?
;; Idea: Collect all actions below.  Project onto ancestors of current node.
;; Can sometimes use goal to know final value, project upwards.  May or may not help.
;; Collect all actions on acyclic paths from (init+projected(w/o goal)) to (projected)

;; How do we handle cycles?  Must go around until nothing changes?

;; How do we compute actions on acyclic paths?  
;; Exists an acyclic path ...

;; Be careful; action with multiple effects must add other effects to sources lists.

(defn make-map-of-sets [keys]
  (let [h (HashMap.)]
    (doseq [key keys] (.put h key (HashSet.)))
    h))

(defn add-mos [#^HashMap mos key val]
  (.add #^HashSet (.get mos key) val))

(defn add-mos-new [#^HashSet dirty #^HashMap oldmos #^HashMap newmos key val]
  (when-not (.contains #^HashSet (.get oldmos key) val)
    (.add dirty key)
    (.add #^HashSet (.get newmos key) val)))

(defn edge-list->map [el]
  (persistent! (reduce (fn [m [k v]] (assoc m k (cons v (m k)))) (transient {}) el)))



(defn exhaustive-dfs [src dst extended-dtg stack-set #^HashSet new-action-pool #^HashSet new-actions]
  (cond (= src dst)               true
        (contains? stack-set src) false
        :else 
          (let [new-stack-set (conj stack-set src)]            
            (some (fn [[nval actions]]
                    (when (exhaustive-dfs nval dst extended-dtg new-stack-set new-action-pool new-actions)
                      (doseq [a actions :when (.contains new-action-pool a)] (.add new-actions a))
                      true))
                  (get extended-dtg src)))))

;; For now, terribly inefficient. 
;; Treating goals specially sould definitaly help.
(defn backward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        extended-dtgs               (domain-transition-graphs vars actions)     
        dead-actions                (HashSet. #^java.util.Collection actions)
        now-live-actions            (HashSet.)
        new-goals                   (make-map-of-sets (keys vars))
        new-srcs                    (make-map-of-sets (keys vars))
        old-goals                   (make-map-of-sets (keys vars))
        old-srcs                    (make-map-of-sets (keys vars))
        dirty-var-set               (HashSet.)]
    (doseq [[var val] init] (add-mos old-srcs var val))
    (add-mos new-goals sas/goal-var-name sas/goal-true-val)
    (.add dirty-var-set sas/goal-var-name)
    (println (count dead-actions))
    
    (while (not (.isEmpty dirty-var-set))
      (let [var (first dirty-var-set)]
        (println "doing" var)
        (while (or (not (.isEmpty #^HashSet (get new-goals var))) (not (.isEmpty #^HashSet (get new-srcs var))))
          (if (not (empty? (get new-goals var)))
            (let [new-goal (first (get new-goals var))]
              (println " doing goal" new-goal)
              (doseq [old-src (get old-srcs var)]
                (assert (exhaustive-dfs old-src new-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove #^HashSet (get new-goals var) new-goal)
              (.add    #^HashSet (get old-goals var) new-goal))
            (let [new-src (first (get new-srcs var))]
              (println " doing src" new-src)              
              (doseq [old-goal (get old-goals var)]
                (assert (exhaustive-dfs new-src old-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove #^HashSet (get new-srcs var) new-src)
              (.add    #^HashSet (get old-srcs var) new-src)))
          (doseq [a (seq now-live-actions)]
            (doseq [[pvar pval] (:precond-map a)]
              (add-mos-new dirty-var-set old-goals new-goals pvar pval))
            (doseq [[evar eval] (:effect-map a)]
              (add-mos-new dirty-var-set old-srcs new-srcs evar eval)))
          (.removeAll dead-actions now-live-actions)
          (.clear now-live-actions))
        (.remove dirty-var-set var)))
    
    (println dead-actions)))

 