(ns angelic.sas.analysis
  (:require [angelic.util :as util]
            [angelic.util [queues :as queues] [graphviz :as gv] [graphs :as graphs]]
            [angelic [sas :as sas] [env :as env]]
            [angelic.env.util :as env-util])
  (:import [java.util HashMap HashSet ArrayList]))


;;;;;;;;;;;;;;;;;;;;;;;;;; Causal graphs, DTGS, etc.          ;;;;;;;;;;;;;;;;;;;;;;;;


(defn domain-transition-graphs 
  "Return a map from var to map from val to map from next-val to seq of actions
   causing this transition."
  ([sas-problem] (domain-transition-graphs (:vars sas-problem) (:actions sas-problem)))
  ([vars actions]
      (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
              (for [a actions
                    [evar eval] (:effect-map a)
                    pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                    :when       (not (= eval pval))]
                [[evar pval eval] a]))))

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
  (let [actions (:actions sas-problem)]
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

(defn effect-clusters [sas-problem]
  (->> (graphs/scc-graph
        (for [a (:actions sas-problem)
              e1 (keys (:effect-map a))
              e2 (keys (:effect-map a))]
          [e1 e2]))
       second vals (map set)))

(defn effect-clustered-causal-graph [sas-problem]
  (let [clusters (effect-clusters sas-problem)
        cluster-map (util/for-map [c clusters, x c] x c)]
    (distinct
     (for [a (:actions sas-problem)
           p (keys (:precond-map a))
           e (keys (:effect-map a))]
       [(cluster-map p) (cluster-map e)]))))

(defn show-effect-clustered-causal-graph [sas-problem]  
  (let [clusters    (effect-clusters sas-problem)
        cluster-map (into {} (for [[i cluster] (util/indexed clusters), x cluster]
                               [x i]))]
    (doseq [[i cluster] (util/indexed clusters)]
      (println i cluster))
    (gv/graphviz-el
     (for [a (:actions sas-problem)
           p (keys (:precond-map a))
           e (keys (:effect-map a))]
       [(cluster-map p) (cluster-map e)]))))

;; TODO: implied truths are over-included.
;;:when (do (util/assert-is (contains? nec-set v)) (> (count nec-set) 1))
(defn auxiliary-vars [sas-problem]
  (dissoc (util/for-map
           [[v nec-set]
            (apply merge-with util/intersection 
                   (for [{:keys [precond-map effect-map]} (:actions sas-problem)
                         p (keys precond-map)]
                     {p (util/union (util/keyset precond-map)
                                    (util/keyset effect-map))}))
            :let [r-set (disj nec-set v)]
            :when (seq r-set)]
           v r-set)
          sas/goal-var-name))


; (doseq [[n p] (sas-sample-problems 0)] (println "\n" n) (let [av (auxiliary-vars p)] (doseq [v av] (println v)) (println (- (count (:vars p)) (count av)))))

(defn prevail-causal-graph [sas-problem]
  (distinct
     (for [a (:actions sas-problem)
           p (keys (apply dissoc (:precond-map a) (keys (:effect-map a))))
           e (keys (:effect-map a))]
       [p e])))
(defn show-prevail-causal-graph [sas-problem] (gv/graphviz-el (prevail-causal-graph sas-problem)))


(defn action-groupings
  "Group actions by the set of variables they effect."
  [sas-problem]
  (group-by #(util/keyset (merge (:precond-map %) (:effect-map %))) (:actions sas-problem)))




  


;;;;;;;;;;;;;;;;;;;;;;;;;;             Homogeneity            ;;;;;;;;;;;;;;;;;;;;;;;;

; An SAS problem is homogenous if every action that affects a particular var
; conditions on the same set of precondition vars.

; For now, we only operate on DAGs, so that each action has exactly one effect.



(defn homogenous? [sas-problem]
  (assert (graphs/dag? (standard-causal-graph sas-problem)))
  (every?
   (fn [[var dtg]]
     (let [actions (apply concat (for [[sv ddtg] dtg, [dv as] ddtg] as))]
       (util/assert-is (apply = #{var} (map (comp util/keyset :effect-map) actions)))
       (apply = (map (comp util/keyset :precond-map) actions))))
   (domain-transition-graphs sas-problem)))


;;;;;;;;;;;;;;;;;;;;;;;;;;             Homogeneity            ;;;;;;;;;;;;;;;;;;;;;;;;

(defn degree [sas-problem]
  (reduce max (map #(count (:effect-map %)) (:actions sas-problem))))

(defn unary? [sas-problem] (<= (degree sas-problem) 1))

;; TODO: do we have to lock preconds ? 
(defn unarize [sas-problem]
  (let [{:keys [ vars init actions]} sas-problem
        cg-edges    (standard-causal-graph sas-problem)
        dep-graph   (graphs/make-undirected-graph
                     (util/keyset vars)
                     (into {} (for [e cg-edges :when (not (apply = e))] [(set e) 1])))
        goal-distances (into {} (for [[e c] (:edges (graphs/shortest-path-graph dep-graph))
                                      :when (contains? e sas/goal-var-name)]
                                  [(first (disj e sas/goal-var-name)) c]))
        final-var-vals (HashMap. (util/map-vals (comp vec :vals) vars))
        final-actions  (ArrayList.)]
    (doseq [a actions]
      (let [{:keys [name precond-map effect-map reward]} a]
        (case (count effect-map)
          1 (.add final-actions a)
          2 (let [primary-evar (apply max-key goal-distances (keys effect-map))
                  primary-eval (util/safe-get effect-map primary-evar)
                  other-evar   (util/safe-singleton (keys (dissoc effect-map primary-evar)))
                  other-eval   (util/safe-get effect-map other-evar)
                  new-val      [:doing name]]
              (.put final-var-vals primary-evar (conj (.get final-var-vals primary-evar) new-val))
              (.add final-actions (env-util/make-factored-primitive
                                   [:start name] precond-map {primary-evar new-val} reward))
              (.add final-actions (env-util/make-factored-primitive
                                   [:aux name] {primary-evar new-val other-evar (util/safe-get precond-map other-evar)} {other-evar other-eval} 0))
              (.add final-actions (env-util/make-factored-primitive
                                   [:finish name] {primary-evar new-val other-evar other-eval} {primary-evar primary-eval} 0))))))
    (sas/make-sas-problem
     (into {} (for [[k v] final-var-vals] [k (sas/make-sas-var k v)]))
     init
     (seq final-actions))))



;(defn homogenize [sas-problem]  
;  )


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
    (queues/pq-add! stack (env-util/make-factored-primitive [:init] {} init 0) 0)
    (while (not (queues/pq-empty? stack))
        (doseq [[var val] (:effect-map (queues/pq-remove-min! stack))
                a (.remove actions-by-precond [var val])]
          (let [c (dec (.remove action-precond-counts a))]
            (if (> c 0)
                (.put action-precond-counts a c)
              (queues/pq-add! stack a 0)))))
;    (println (util/map-vals count (group-by first  untested-vals)))
    (println (count unset-vals) (count untested-vals) (count actions-by-precond) (count action-precond-counts))
    [untested-vals (concat unset-vals (keys actions-by-precond)) (keys action-precond-counts)]))



;;;;;;;;;;;;;;;;;;;;;;;;;; Static analysis for finding equivalent vals ;;;;;;;;;;;;;;;;;;;;;;;;

;; Do static look at actions and find equivalent vals
 ; These are: ones that are always set at the same time, AND
 ; all ways of unsetting them unset both.  Slow for now.
(defn canonical-vv [pair] (sort-by first pair))

(defn find-static-equivalence-pairs [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        actions                     (cons (env-util/make-factored-primitive [:init] {} init 0) actions)
        extended-dtgs               (domain-transition-graphs vars actions)
        extended-rdtgs              (reverse-domain-transition-graphs vars actions)]
    (filter
     (fn [[[var1 val1] [var2 val2]]]
       (when (< (.compareTo ^Comparable var1 ^Comparable var2) 0)
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
    (loop [remaining-map (util/map-vals #(set (map second %)) (group-by first symmetric-pairs)), results nil]
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
                                                  (group-by first (apply concat equiv-sets)))))
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



;;;;;;;;;;;;;;;;;;;;;;;;;; Static analysis for finding implications ;;;;;;;;;;;;;;;;;;;;;;;;

;; u=x --> v=y if:
;;   whenever v is set to y, u is set to x, or u is not set and has precond x
;;   whenever v is set to not y, either u is already not x, or u is set to not x.

;; Candidates [x y] where maybe x ==> y
(defn find-candidate-implications [actions]
  (->> (for [{:keys [precond-map effect-map]} actions
             :let [final-map (merge precond-map effect-map)]
             [evar eval] effect-map]
         [[evar eval] (set (dissoc final-map evar))])
       (group-by first)
       (util/map-vals #(apply util/intersection (map second %)))
       (graphs/outgoing-map->edge-list)))

(defn valid-implication? [extended-dtgs [[u x] [v y]]]
  (every? (fn [{:keys [precond-map effect-map]}]
            (when-let [u-val ((merge precond-map effect-map) u)]
              (not (= u-val x))))                
          (apply concat (vals (get-in extended-dtgs [v y])))))



(defn find-static-implications [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        actions                     (cons (env-util/make-factored-primitive [:init] {} init 0) actions)]    
    (->> (find-candidate-implications actions)
;         (map util/prln)
         (filter (partial valid-implication? (domain-transition-graphs vars actions)))
         (graphs/edge-list->outgoing-map)
         (util/map-vals (partial into {})))))

;; Unfortunately, that's not good enough for what we need.  Need to be able to track implications.
;; So, we need a fixed point algorithm
;; Basic idea will be to track, for each variable and value,
;; allowed values for each other variable.
;; Initially suppose nothing but initial state is allowed.
;; Can do this with a quiescence search?
;; Action is allowed when all combinatinos of preconds are allowed.
;;  It creates combinations of all effect values,
;;  Plus effect values with unchanged precondition values,
;;  Plus effect values with all other values not ruled out by preconditions.

;; Use planning-graph-type thing
;; initialize with single, pairs of values from initial state,
;; each value or pair may enable an action
;;  plus pair of action and all currently applicable persists.
;; action enables outcomes and all pairs
;; action + persist enables pairs
;; pairs enable action + persists.
;; Implement it as await counts.

;; action awaits all individuals + pairs.
;; value awaits any action
;; action + persist awaits all pairs of precond + other
;; value pair awaits producing action or action + persist

(set! *warn-on-reflection* true)

(defn single-value [v] [:v v])
(defn mutex-value [v1 v2] [:vm #{v1 v2}])
(defn single-action [a] [:a a])
(defn mutex-action [a pv] [:am a pv])

(defn initial-items [init actions]
  (concat
   (for [kv init] (single-value kv))
   (for [[v1 v2] (util/combinations init 2)] (mutex-value v1 v2))
   (for [a actions :when (empty? (:precond-map a))] (single-action a))))


(defn predecessors-and-counts [vars actions implications]
  (let [rdtgs (reverse-domain-transition-graphs vars actions)
        vv-pairs (for [v (vals vars), vl (:vals v)] [(:name v) vl])]
    (concat
     (for [vv vv-pairs]
       [(single-value vv)
        1
        (for [a (apply concat (vals (get-in rdtgs vv)))]
          (single-action a))])

     (for [[[vr1 vl1 :as vv1] [vr2 vl2 :as vv2]] (util/combinations vv-pairs 2)
           :when (not (= vr1 vr2))
           :let [imp2 (get-in implications [vv1 vr2] vl2)
                 imp1 (get-in implications [vv2 vr1] vl1)]]
       [(mutex-value vv1 vv2)
        (if (and (= imp1 vl1) (= imp2 vl2)) 1 Double/POSITIVE_INFINITY)
        (for [a (distinct (concat (apply concat (vals (get-in rdtgs vv1)))
                                  (apply concat (vals (get-in rdtgs vv2)))))]
          (let [{:keys [precond-map effect-map]} a
                persist-map (into precond-map effect-map)]
            (cond (and (= (persist-map vr1) vl1) (= (persist-map vr2) vl2))
                  (single-action a) 
                  (= (persist-map vr1) vl1) (mutex-action a vv2)
                  (= (persist-map vr2) vl2) (mutex-action a vv1)
                  :else (assert nil))))])

     (for [a actions
           :let [{:keys [precond-map effect-map]} a
                 preds (concat
                        (map single-value precond-map)
                        (map (fn [[vv1 vv2]] (mutex-value vv1 vv2)) (util/combinations precond-map 2)))]]
       [(single-action a) (count preds) preds])

     (for [a actions,
           :let [{:keys [precond-map effect-map]} a]
           [vr vl :as vv] vv-pairs
           :when (and (not (contains? precond-map vr))
                      (not (contains? effect-map vr)))
           :let [preds (for [pvv precond-map] (mutex-value vv pvv))]]
       [(mutex-action a vv) (count preds) preds]))))


(defn find-mutexes [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        implications {} ;        (find-static-implications sas-problem) ;; Doesn't actually help, when fixed...
        counts (HashMap.)
        open   (ArrayList.)
        successors (HashMap.)
        closed     (HashSet.)]

    (doseq [[x cnt preds] (predecessors-and-counts vars actions implications)]
      (assert (> cnt 0))
      (.put counts x cnt)
      (doseq [pred preds]
        (.put successors pred (cons x (.get successors pred)))))
    
    (doseq [i (initial-items init actions)]
      (.remove counts i)
      (.add open i))       

    (while (> (.size open) 0)
      (let [x  (.remove open (int (dec (.size open))))]
;        (println x)
        (assert (not (.contains closed x)))
        (.add closed x)
        (doseq [s (.remove successors x)]
          (when-let [c (.remove counts s)]
            (if (> c 1)
              (.put counts s (dec c))
              (.add open s))))))

    (comment
      (println (count successors) (count counts) (count closed))
      
      (clojure.inspector/inspect-tree
       (for [[x cnt preds] (predecessors-and-counts vars actions implications)
             :when (and (= (first x) :a)
                        (not (.contains closed x)))]
         [x (filter #(not (.contains closed %)) preds)]))
    
      (->> closed
           (filter #(= (first %) :v))
           (map second)
           (group-by first)
           (util/map-vals (partial map second))))

    (let [{:keys [v vm a]} (util/map-vals (partial map second)
                                             (group-by first (keys counts)))]
      [(util/map-vals (comp set (partial map second)) (group-by first v)) 
       (reduce (fn [m [[vr1 vl1] [vr2 vl2]]]
                 (assoc-in m [[vr1 vl1] vr2 vl2] true))
               {}
               (mapcat util/permutations vm))
       a])))


(defn compute-implications [vars mutexes]
  (->>
   (util/map-vals
    (fn [m] 
      (into {}
            (for [[k vs] m
                  :let [r-vals (clojure.set/difference (set (:vals (vars k))) (util/keyset vs))]
                  :when (<= (count r-vals) 1)]
              [k (util/safe-singleton r-vals)])))
    mutexes)   
   (filter #(seq (val %)))
   (into {})))





(defn find-implications [sas-problem]
  (compute-implications (:vars sas-problem) (second (find-mutexes sas-problem))))




(set! *warn-on-reflection* false)





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

(defn add-mos [^HashMap mos key val]
  (.add ^HashSet (.get mos key) val))

(defn add-mos-new [^HashSet dirty ^HashMap oldmos ^HashMap newmos key val]
  (when-not (.contains ^HashSet (.get oldmos key) val)
    (.add dirty key)
    (.add ^HashSet (.get newmos key) val)))

(defn edge-list->map [el]
  (persistent! (reduce (fn [m [k v]] (assoc m k (cons v (m k)))) (transient {}) el)))



(defn exhaustive-dfs [src dst extended-dtg stack-set ^HashSet new-action-pool ^HashSet new-actions]
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
        dead-actions                (HashSet. ^java.util.Collection actions)
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
        (while (or (not (.isEmpty ^HashSet (get new-goals var))) (not (.isEmpty ^HashSet (get new-srcs var))))
          (if (not (empty? (get new-goals var)))
            (let [new-goal (first (get new-goals var))]
              (println " doing goal" new-goal)
              (doseq [old-src (get old-srcs var)]
                (assert (exhaustive-dfs old-src new-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove ^HashSet (get new-goals var) new-goal)
              (.add    ^HashSet (get old-goals var) new-goal))
            (let [new-src (first (get new-srcs var))]
              (println " doing src" new-src)              
              (doseq [old-goal (get old-goals var)]
                (assert (exhaustive-dfs new-src old-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove ^HashSet (get new-srcs var) new-src)
              (.add    ^HashSet (get old-srcs var) new-src)))
          (doseq [a (seq now-live-actions)]
            (doseq [[pvar pval] (:precond-map a)]
              (add-mos-new dirty-var-set old-goals new-goals pvar pval))
            (doseq [[evar eval] (:effect-map a)]
              (add-mos-new dirty-var-set old-srcs new-srcs evar eval)))
          (.removeAll dead-actions now-live-actions)
          (.clear now-live-actions))
        (.remove dirty-var-set var)))
    
    (println dead-actions)))

 