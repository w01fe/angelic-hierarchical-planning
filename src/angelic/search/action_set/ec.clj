(ns angelic.search.action-set.ec
  (:require [angelic.util :as util]
            [angelic.util.queues :as queues]
            [angelic.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis]
            [angelic.search.action-set.asplan :as asplan]
            )
  (:import [java.util HashSet HashMap  ArrayList]))

;; This implements (inefficiently) the expansion core strategy of 
;; Chen et al. (2009), for comparing # states generated with BI.

(set! *warn-on-reflection* true)

(defn effect-var [a] (util/safe-singleton (keys (:effect-map a))))

(defn potential-precondition-edges [state pde-map ap-map]
  (for [[var val :as p] (state/as-map state)
        a               (get ap-map p)
        :let [[evar eval] (util/safe-singleton (:effect-map a))
              pval        (util/safe-get (:precond-map a) evar)]
        :when (get-in pde-map [evar (state/get-var state evar) [pval eval]])]
    [var evar]))

(defn potential-dependent-edges [state pdv-map dtgs]
  (for [[var val :as p] (state/as-map state)
        [_ as]          (get-in dtgs [var val])
        a               as
        [pvar pval]     (:precond-map a)
        :when           (and (not (= pvar var))
                             (get-in pdv-map [pvar (state/get-var state pvar) pval]))]
    [var pvar]))

(defn potential-dependency-graph [state pde-map pdv-map ap-map dtgs]
  (set (concat (potential-precondition-edges state pde-map ap-map)
               (potential-dependent-edges state pdv-map dtgs))))

(defn best-core [pdg-edges goal-var-set]
  (let [[scc-edges scc-nodes] (graphs/scc-graph pdg-edges)
        scc-edge-map (graphs/edge-list->outgoing-map scc-edges)]
;    (println "\n" goal-var-set scc-edges scc-nodes pdg-edges)
    (apply min-key count
           (for [[scc-id scc-vars] scc-nodes
                 :when (some goal-var-set scc-vars)]
             (let [s (apply concat
                    (for [downstream-scc-id (graphs/postwalk [scc-id] scc-edge-map)]
                      (util/safe-get scc-nodes downstream-scc-id)))]
;               (println s)
               s)))))


(defn ec-prune-actions [state actions pde-map pdv-map ap-map dtgs goal-var-set]
  (let [pdg-edges (potential-dependency-graph state pde-map pdv-map ap-map dtgs)
        core-var-set (set (best-core pdg-edges goal-var-set))]
    (filter
     #(contains? core-var-set (effect-var %))       
     actions)))

;; goal-val is ::none if not goal-related.
(defn potential-descendant-vars [dtg goal-val]
  (let [dtg-om  (util/map-vals keys dtg)
        backward-set (set  (if (= goal-val ::none)
                             (keys dtg-om)
                             (graphs/postwalk
                              [goal-val]
                              (-> dtg-om
                                  graphs/outgoing-map->edge-list
                                  graphs/edge-list->incoming-map))))]        
    (into {} (for [v (keys dtg-om)]
               [v (util/intersection backward-set (set (graphs/postwalk [v] dtg-om)))]))))

(defn potential-acyclic-descendant-vars [dtg goal-val]
  (let [dtg-om  (util/map-vals keys dtg)
        dtg-edges (graphs/outgoing-map->edge-list dtg-om)
        dtg-edge-map (if (= goal-val ::none)
                       (util/map-vals (constantly dtg-edges) dtg-om)
                       (into {} (for [v (keys dtg-om)]
                                  [v (graphs/eliminate-some-cyclic-edges dtg-edges v goal-val)])))]        
    (into {} (for [[v e] dtg-edge-map]
               [v (set (graphs/postwalk [v] (graphs/edge-list->outgoing-map e)))]))))

(defn pdv-map->pde-map [pdv-map dtgs]
  (into {} (for [[var pdv] pdv-map]
             [var (into {} (for [[val dvs] pdv]
                             [val (set (for [v dvs
                                             nv (keys (get-in dtgs [var val]))
                                             :when (contains? pdv nv)]
                                         [v nv]))]))])))

(defn ec-search [sas-problem use-new-goal acyclic-pruning]
  (let [q             (queues/make-tree-search-pq)
        closed        (HashSet.)
        actions       (env/actions-fn sas-problem)
        dtgs          (sas-analysis/domain-transition-graphs sas-problem)
        goal-map      (assoc
                          (if use-new-goal
                            {}
                            (->> (:actions sas-problem)
                                 (filter #(= (:name %) sas/goal-action-name))
                                 util/safe-singleton :precond-map))
                        sas/goal-var-name sas/goal-true-val)        
        pdv-map       (into {} (for [[var dtg] dtgs]
                                 [var (if acyclic-pruning
                                        (potential-acyclic-descendant-vars dtg (get goal-map var ::none))
                                        (potential-descendant-vars dtg (get goal-map var ::none)))]))
        pde-map       (pdv-map->pde-map pdv-map dtgs)
        ap-map        (HashMap.)
        goal          (env/goal-fn sas-problem)]
    (assert (not acyclic-pruning)) ;; Seems incorrect anyway.
    (when acyclic-pruning (assert (not use-new-goal)))
    (doseq [a (:actions sas-problem), pp (:precond-map a)]
      (.put ap-map pp (cons a (.get ap-map pp))))    
    (queues/pq-add! q (env/initial-state sas-problem) 0)
    (loop []
      (when-not (queues/pq-empty? q)
        (let [[state c] (queues/pq-remove-min-with-cost! q)]
          (util/print-debug 3 "dequeueing " (:act-seq (meta state)) c  state "\n" (Thread/sleep 100))
          (if (goal state)
            [(reverse (:act-seq (meta state))) (:reward (meta state))]
            (do (when-not (.contains closed state)
                  (.add closed state)
                  (doseq [a (ec-prune-actions state (actions state) pde-map pdv-map ap-map dtgs
                                              (set (for [[gvar gval] goal-map
                                                         :when (not (= gval (state/get-var state gvar)))]
                                                     gvar)))]
                    (let [[ss sc] (env/successor a state)]
                      (queues/pq-add! q ss (- c sc)))))
                (recur))))))))



;; (use 'angelic.env 'angelic.domains.taxi-constrained 'angelic.domains.sas-problems 'angelic.search.action-set.ec)

;; (let [e (force (nth ipc2-logistics 3)) ]  (println (time (run-counted #(ec-search e false)))))

;; (let [e  (make-random-pairwise-taxi-env 3 3 2 true 1)] (doseq [t [:simple :dynamic :fluid]] (println "\n"  t (time (run-counted #(stratified-search e t))))))


;;(doseq [ i [5 7 2 4 1 0 9 6 8 3]] (let [e  (force (nth ipc2-logistics i))] (println "\n\n" i) (doseq [t [:simple #_ :dynamic :fluid]] (println "\n"  t (time (run-counted #(stratified-search e t)))))))

;; Logistics results (# states) to match table. 
;; 5 5-2: 2015
;; 7 6-1: 161014
;; 2 4-2: 352896
;; 4 5-1: 625680
;; 1 4-1: 
;; 0 4-0: 1710618
;; 9 6-3: 3476092
;; 6 6-0: 
;; 8 6-2: 
;; 3 5-0: 4706820

;; Note: no benefit if we add goal action :).


;; With acyclic path removal:
;; 5 5-2: 2085
;; 7 6-1: 83553
;; 2 4-2: 411304
;; 4 5-1: 364847
;; 1 4-1: 
;; 0 4-0: 1710618
;; 9 6-3: 3476092
;; 6 6-0: 
;; 8 6-2: 
;; 3 5-0: 4706820
