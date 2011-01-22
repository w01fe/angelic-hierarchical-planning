(ns angelic.search.action-set.stratified
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [edu.berkeley.ai.util.graphs :as graphs]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.sas :as sas]
            [angelic.sas.analysis :as sas-analysis]
            [angelic.search.action-set.asplan :as asplan]
            )
  (:import [java.util HashSet HashMap  ArrayList]))

;; This implements (inefficiently) the stratified planning strategy of 
;; Chen et al. (2009), for comparing # states generated with BI.

(set! *warn-on-reflection* true)

(defn effect-var [a] (util/safe-singleton (keys (:effect-map a))))

;; TODO: none of these work!
(defn dynamic-inf-stratified-applicable-actions [last-a state tsi av-map ap-map actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)
          e-p-set (set (for [b (get ap-map (util/safe-singleton (seq (:effect-map last-a))))
                             [pvar pval] (:precond-map b)
                             :when (not (= (state/get-var state pvar) pval))]
                         pvar))
          p-set   (apply clojure.set/union (map av-map e-p-set))]
      (util/prln (filter
        (fn [b]
          (let [b-var (effect-var b)
                b-level (util/safe-get tsi b-var)]
            (or (and (<= b-level a-level) (contains? p-set b-var))
                (contains? (util/keyset (:precond-map b)) (keys (:precond-map last-a)))
                (contains? (:precond-map b) a-var))))       
        (actions state)) last-a))
    (actions state)))

(comment (some #(= ((:precond-map last-a) %) ((:precond-map b) %))
            (clojure.set/intersection (util/keyset (:precond-map last-a)) (util/keyset (:precond-map b)))))

;; TODO: Is this actually right -- i think not?
(defn improved-inf-stratified-applicable-actions [last-a state tsi cav-map actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)
          p-set   (util/safe-get cav-map a-var)]
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (and (<= b-level a-level)  (contains? p-set b-var))
               (contains? (:precond-map b) a-var))))       
       (actions state)))
    (actions state)))

(defn inf-stratified-applicable-actions [last-a state tsi actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)]
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (<= b-level a-level)
               (contains? (:precond-map b) a-var))))       
       (actions state)))
    (actions state)))

(defn stratified-search [sas-problem type]
  (assert (#{:simple} type))
  (let [q       (queues/make-tree-search-pq)
        closed  (HashSet.)
        actions (env/actions-fn sas-problem)
        causal-graph  (sas-analysis/standard-causal-graph sas-problem)
        cg-map        (graphs/edge-list->outgoing-map causal-graph)
        av-map        (into {} (for [v (keys (:vars sas-problem))]
                                 [v (graphs/ancestor-set causal-graph [v])]))
        cav-map       (into {} (for [v (keys (:vars sas-problem))]
                                 [v (apply clojure.set/union (map av-map (cg-map v)))]))
        ap-map        (HashMap.)
;        pre-var-map   (util/map-vals #(set (map first %)) (group-by second causal-graph))
        tsi           (graphs/topological-sort-indices (remove #(apply = %) causal-graph))
        goal    (env/goal-fn sas-problem)
        init    (env/initial-state sas-problem)
        strat-actions (case type
                        :simple     (fn [last-a state] (inf-stratified-applicable-actions last-a state tsi actions))
                        :structural (fn [last-a state] (improved-inf-stratified-applicable-actions last-a state tsi cav-map actions))                       :dynamic    (fn [last-a state] (dynamic-inf-stratified-applicable-actions last-a state tsi av-map ap-map actions)))]
    (when (= type :dynamic) #_ (println av-map)
      (doseq [a (:actions sas-problem), pp (:precond-map a)]
        (.put ap-map pp (cons a (.get ap-map pp)))))    
    (queues/pq-add! q [nil init] 0)
;    (println causal-graph tsi pre-var-map)
    (loop []
      (when-not (queues/pq-empty? q)
        (let [[[last-a state] c] (queues/pq-remove-min-with-cost! q)]
          (util/print-debug 3 "dequeueing " (:act-seq (meta state)) c last-a state "\n")
          (if (goal state)
            [(reverse (:act-seq (meta state))) (:reward (meta state))]
            (do (when-not (.contains closed state)
                  (.add closed state)
                  (doseq [a (strat-actions last-a state)]
                    (when (env/applicable? a state)
                      (let [[ss sc] (env/successor a state)]
                        (queues/pq-add! q [a ss] (- c sc))))))
                (recur))))))))



;; (use 'angelic.env 'angelic.domains.taxi-infinite 'angelic.domains.sas-problems 'angelic.search.action-set.stratified)

;; (let [e (force (nth ipc2-logistics 3)) ]  (println (time (run-counted #(stratified-search e)))))

;; Logistics results (# states) to match table. -- ordi
;; 5-2: 19771
;; 6-1: 226446
;; 4-2: 365709
;; 5-1: 677522
;; 4-1: 1030555
;; 4-0: 1281114
;; 6-3: 2747824
;; 6-0: 3435578
;; 6-2: 3286212
;; 5-0: 4053436

;; Wrong ? 
;; Logistics results (# states) to match table. -- structural
;; 5-2: 8585
;; 6-1: 226446
;; 4-2: 122924
;; 5-1: 390726
;; 4-1: 414577
;; 4-0: 646398
;; 6-3: 2747824
;; 6-0: 3435578
;; 6-2: 3286212
;; 5-0: 3085333

;; Logistics results (# states) to match table. -- dynamic
;; 5-2: 2895
;; 6-1: 34968
;; 4-2: 74947
;; 5-1: 
;; 4-1: 
;; 4-0: 
;; 6-3: 
;; 6-0: 
;; 6-2: 
;; 5-0: 