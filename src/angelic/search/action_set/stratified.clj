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

(defn dynamic-inf-stratified-applicable-actions [last-a state tsi av-map ap-map actions]
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)
          p-set   (dynamic-var-set state av-map ap-map a-var)]
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (and (<= b-level a-level) (contains? p-set b-var))
               (contains? (:precond-map b) a-var))))       
       (actions state)))
    (actions state)))

(defn fluid-predecessors [state ap-map v]
  (apply clojure.set/intersection
         (for [a (util/safe-get ap-map [v (state/get-var state v)])
               :when (contains? (:effect-map a) v)]
           (set (for [[pvar pval] (:precond-map a)
                      :when (and (not (= pvar v)) (not (= pval (state/get-var state pvar))))]
                  pvar)))))

;; TODO: dead vars?
;; Fluid iff *all* children fluid? Yes.
;; Idea: take min-level fluid var, everything <=-level, everything in CC.  Toss everything else.

;; Fluid vars are those whose value must change, and current value is useless.
;; Ideally, we would take dead vars into account here too.
(defn fluid-vars [state ap-map cg-map goal]
  (let [open   (ArrayList.)
        closed (HashSet.)
        fluid-child-count-map (HashMap.)]
    (doseq [[var val] goal]
      (when-not (= val (state/get-var state var))
        (.add open var)))
    (while (not (.isEmpty open))
      (let [v (.remove open (dec (count open)))]
        (when-not (.contains closed v)
          (.add closed v)
          (doseq [p (fluid-predecessors state ap-map v)]
            (let [oc (get fluid-child-count-map p 0)]
              (if (= oc (dec (count (cg-map p))))
                (.add open p)
                (.put fluid-child-count-map p (inc oc))))))))
    (set (seq closed))))

(defn dynamic-fluid-var-set [state av-map ap-map f]
  (let [open   (ArrayList.)
        ret    (HashSet.)
        closed (HashSet.)]
    (.addAll open (av-map f))
    (.addAll ret  (av-map f))
    (while (not (.isEmpty open))
      (let [v (.remove open (dec (count open)))]
        (when-not (.contains closed v)
          (.add closed v)
          (doseq [x (dynamic-predecessors state ap-map v)]
            (.addAll ret (av-map x))
            (.addAll open (av-map x))))))
    (set (seq ret))))

(comment
 (defn connected-component [domain seeds cg-map icg-map]
   (let [open   (ArrayList.)
         closed (HashSet.)]
     (doseq [v seeds]
       (.addAll open seeds))
     (while (not (.isEmpty open))
       (let [v (.remove open (dec (count open)))]
         (when (and (not (.contains closed v)) (contains? domain v))
           (.add closed v)
           (.addAll open (cg-map v))
           (.addAll open (icg-map v)))))
     (set (seq closed)))))

(defn fluid-source [fluid-set tsi icg-map v]
  (if-let [fluid-parents (seq (filter fluid-set (icg-map v)))]
    (recur fluid-set tsi icg-map (apply max-key tsi fluid-parents))
    v))

(defn fluid-prune [p-set state tsi av-map ap-map goal cg-map icg-map]
  (let [fluid-set   (fluid-vars state ap-map cg-map goal)
        fluid-p-set (clojure.set/intersection p-set fluid-set)]
;    (println fluid-set)
    (if (seq fluid-p-set)
      (let [root-fluid (apply max-key tsi fluid-p-set)
            source-fluid (fluid-source fluid-p-set tsi icg-map root-fluid)
;            rfs (set (concat (filter #(> (tsi %) (tsi root-fluid)) p-set)
;            (dynamic-fluid-var-set state av-map ap-map root-fluid)))
            sfs (set (concat (filter #(> (tsi %) (tsi source-fluid)) p-set)
                             (dynamic-fluid-var-set state av-map ap-map source-fluid)))]
;        (println "\n" root-fluid source-fluid rfs sfs)
;        #_(when-not (= rfs sfs) (println "\n" root-fluid rfs "\n" source-fluid sfs "\n" (filter #(> (tsi %) (tsi source-fluid)) p-set)
;        (dynamic-fluid-var-set state av-map ap-map source-fluid)))
        sfs )     
      p-set)))


(defn dynamic-fluid-inf-stratified-applicable-actions [last-a state tsi av-map ap-map goal cg-map icg-map actions]
  ;; Root set ignored for now -- doing it dynamically.
  (if last-a
    (let [a-var   (effect-var last-a)
          a-level (util/safe-get tsi a-var)
          p-set   (fluid-prune (dynamic-var-set state av-map ap-map a-var)
                               state tsi av-map ap-map goal cg-map icg-map)]
;      (println "\n" last-a fluid-set fluid-root-set p-set state)
      (filter
       (fn [b]
         (let [b-var (effect-var b)
               b-level (util/safe-get tsi b-var)]
           (or (contains? (:precond-map b) a-var) 
               (and (<= b-level a-level) (contains? p-set b-var)))))       
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
  (assert (#{:simple :dynamic :fluid} type))
  (let [q       (queues/make-tree-search-pq)
        closed  (HashSet.)
        actions (env/actions-fn sas-problem)
        causal-graph  (sas-analysis/standard-causal-graph sas-problem)
        noeq-causal-graph (remove (fn [[v c]] (= v c)) causal-graph)
        cg-map        (graphs/edge-list->outgoing-map noeq-causal-graph)
        icg-map       (graphs/edge-list->incoming-map noeq-causal-graph)        
        av-map        (into {} (for [v (keys (:vars sas-problem))]
                                 [v (graphs/ancestor-set causal-graph [v])]))
        cav-map       (into {} (for [v (keys (:vars sas-problem))]
                                 [v (apply clojure.set/union (map av-map (cg-map v)))]))
        ap-map        (HashMap.)
;        pre-var-map   (util/map-vals #(set (map first %)) (group-by second causal-graph))
        tsi           (graphs/df-topological-sort-indices (remove #(apply = %) noeq-causal-graph))
        goal-map (:precond-map (util/safe-singleton (filter #(= (:name %) sas/goal-action-name) (:actions sas-problem))))
        goal    (env/goal-fn sas-problem)
        init    (env/initial-state sas-problem)
        strat-actions (case type
                        :simple     (fn [last-a state] (inf-stratified-applicable-actions last-a state tsi actions))
                        :structural (fn [last-a state] (improved-inf-stratified-applicable-actions last-a state tsi cav-map actions))                       :dynamic    (fn [last-a state] (dynamic-inf-stratified-applicable-actions last-a state tsi av-map ap-map actions))
                        :fluid    (fn [last-a state] (dynamic-fluid-inf-stratified-applicable-actions last-a state tsi av-map ap-map goal-map cg-map icg-map actions))
                        )]
    (println tsi)
    (when (#{:dynamic :fluid} type) #_ (println av-map)
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

;; Logistics results (# states) to match table. -- dynamic AND fluid
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





;; Wrong!
;; Logistics results (# states) to match table. -- fluid
;; 5 5-2: 10230
;; 7 6-1: 96430
;; 2 4-2: 182321
;; 4 5-1: 229929
;; 1 4-1: 324127
;; 0 4-0: 473231
;; 9 6-3: 1087515
;; 6 6-0: 899623
;; 8 6-2: 903447
;; 3 5-0: 1155503



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
