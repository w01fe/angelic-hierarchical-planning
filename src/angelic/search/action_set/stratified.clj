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

(defn dynamic-predecessors [state ap-map v]
  (for [a (get ap-map [v (state/get-var state v)])
        [pvar pval] (:precond-map a)
        :when (not (= (state/get-var state pvar) pval))]
    pvar))

(defn dynamic-var-set [state av-map ap-map v]
  (let [open   (ArrayList.)
        ret    (HashSet.)
        closed (HashSet.)]
    (.add open v)
    (while (not (.isEmpty open))
      (let [v (.remove open (dec (count open)))]
        (when-not (.contains closed v)
          (.add closed v)
          (doseq [x (dynamic-predecessors state ap-map v)]
            (.addAll ret (av-map x))
            (.addAll open (av-map x))))))
    (set (seq ret))))

;; TODO: none of these work!
(defn dynamic-inf-stratified-applicable-actions [last-a state tsi av-map ap-map actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)
          p-set   (dynamic-var-set state av-map ap-map a-var)]
   #_   (println last-a p-set state)
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (and (<= b-level a-level) (contains? p-set b-var))
;               (contains? (util/keyset (:precond-map b)) (keys (:precond-map last-a)))
               (contains? (:precond-map b) a-var))))       
       (actions state)))
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
  (assert (#{:simple :dynamic} type))
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

;; Logistics results (# states) to match table. -- dynamic
;; 5-2: 16086
;; 6-1: 194870
;; 4-2: 277791
;; 5-1: 454016
;; 4-1: 750217
;; 4-0: 986574
;; 6-3: 1908549
;; 6-0: 1864844
;; 6-2: 1947242
;; 5-0: 2272572




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
