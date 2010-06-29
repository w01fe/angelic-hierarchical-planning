(ns exp.simple-dag-hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Types, Protocols, Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: in purely static analysis, either cannot prune source vals, or must 
;; split HLAs.  Here, this amounts to, more or less, just removing outgoing arcs from goal.

;; TODO: actual precond var set may not go all the way back to sources... shoudl take this into account.  Should relax these where possible. 

;; TODO: more sophisticated interleaveing-condition based on dynamic descendent set.

;; TODO: immediate refinemetns wrapper that chases chains.
 ; or, resolve tension between greediness and maximal caching? 

;; Currently, was written as if we've always done as much greedy stuff as possible, leave ourselves with a choice of leaf preconds.
;; Problem is, e.g., in source var this means we lose caching.
;; Also problems when we have moved something out front, would rather not hypothetically clean up current

; One option: always expand, may leave greedy
; problem: this duplicates lots of work.

; Another option: always take greedy, can leave unexpanded.
; seems better.  Would like to pull all greedy, but then we have to simulate action.
; Better to pull at most one? 
; Actions can store if they have greedy /unexpanded bits.





;; TODO: this is fundamentlaly broken, since it doesn't do "lookahead".


(declare make-action-hla)

(deftype Simple-DAG-Hierarchy 
  [sas-problem 
   predecessor-var-set
   ancestor-var-set
   var-levels
   interfering-set ; fn from var to set of vars: descendents of ancestors but not descendents. 
   dtg-to       ; fn from var & dst-val to map from cur-val to map from nxt-val to actions
   cycle-to     ; from from var & dst-val to map from cur-val to bool, if can cycle from cur-val
   greedy-optimization?])

(defn make-simple-dag-hierarchy 
  ([sas-problem] (make-simple-dag-hierarchy sas-problem true))
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


(defprotocol SDH-HLA
  (active-var-set  [a])
  (leaf-var-set    [a])
  (greedy?         [a s v av])    ; Has a descendent that can be done greedily.
  (do-refinement   [a s v av lv]) ;returns [action-seq new-hla]. av is active-var set, lv is leaf-var set
  ) 




(defprotocol SDH-Precond-HLA
  (active?    [a])
  (satisfied? [a s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Active Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ?Note, for bookkeeping to work properly we have to retain an active precond in an action even if we have also pushed it out front.

; first-action can be null, iff we're done.

;; Which function to calal for recursive i-r.  Should probably be hierarchy/immediate-refs.

;; Note: can get primitives 

(defn rec-immediate-refinements [a s]
  (hierarchy/immediate-refinements- a s))

(defn effect-val [a]
  (val (util/safe-singleton (:effect-map (if (env/primitive? a) a (:action a) )))))

(declare make-active-precond-hla)

(deftype SDH-Active-Precond-HLA  [hierarchy name first-action leaf-precond active-var-set leaf-var-set] :as this
  SDH-HLA
    (active-var-set  []  (conj active-var-set (:var leaf-precond)))
    (leaf-var-set    []  leaf-var-set)
    (greedy?         [s v av] 
       (and first-action (or (env/primitive? first-action) (greedy? first-action s v av))))
    (do-refinement   [s v av lv]
       (if (empty? (clojure.set/intersection lv ((:interfering-set hierarchy) (:var leaf-precond))))
           [[[leaf-precond] (make-active-precond-hla hierarchy nil leaf-precond)]]                   
         (for [[prefix new-fa] (if (env/primitive? first-action) 
                                   [[first-action] nil]
                                 (do-refinement first-action s v av lv))
               new-fa          (if new-fa [new-fa] (map first (rec-immediate-refinements leaf-precond (env/set-var s (:var leaf-precond) (effect-val first-action)))))]
           [prefix (make-active-precond-hla hierarchy new-fa leaf-precond)])))
  SDH-Precond-HLA  
    (active?     []  true)
    (satisfied?  [s]
      (assert (= (not first-action) (satisfied? leaf-precond s)))
      (not first-action))    
  env/Action
    (action-name [] name)
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (env/precondition-context leaf-precond s)))

(defn- make-active-precond-hla [hierarchy first-action leaf-precond]
  (SDH-Active-Precond-HLA hierarchy 
    [:!P* (when first-action (env/action-name first-action)) (env/action-name leaf-precond)]
    first-action leaf-precond
    (conj (if first-action (active-var-set first-action) #{}) (:var leaf-precond))
    (if first-action (leaf-var-set first-action) #{})))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Leaf Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype SDH-Leaf-Precond-HLA  [hierarchy name var dst-val dtg precond-var-set] :as this
  SDH-HLA
    (active-var-set  []  #{})
    (leaf-var-set    []  #{var})
    (greedy?         [s v av] false)
    (do-refinement   [s v av lv]
      (assert (= v var))
      (if (empty? (clojure.set/intersection lv ((:interfering-set hierarchy) var)))
           [[[this] (make-active-precond-hla hierarchy nil this)]] 
         (for [[a _] (rec-immediate-refinements this s)]
           [[] (make-active-precond-hla hierarchy a this)])))
  SDH-Precond-HLA 
    (active?     []  false)
    (satisfied?  [s] (= (env/get-var s var) dst-val))    
  env/Action
    (action-name [] name)
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] precond-var-set)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] 
      (let [cur-val (env/get-var s var)]
;        (println cur-val dst-val)
        (if (= cur-val dst-val)
            [[]]
          (for [as (vals (get dtg cur-val)), action as]
            [(make-action-hla hierarchy action) this]))))
    (cycle-level-           [s] 
      (when ((:cycle-to hierarchy) var dst-val)
        ((:var-levels hierarchy) var))))

(defn- make-leaf-precond-hla [hierarchy var dst-val]
  (SDH-Leaf-Precond-HLA hierarchy [:!P var dst-val] var dst-val 
                   ((:dtg-to           hierarchy) var dst-val)
                   ((:ancestor-var-set hierarchy) var)))

;; TODO: when can greedy sat arise?  After creation, other-sat, or finish


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: actions need to fire; immediately; after completion of a precondition; greedily; ...
;; TODO: fire more than one greedy action at once ...
; ;TODO: how do we keep track of preconditions moved up front ?

; Am I greedy, or do I have a 
(declare make-action-hla)

(deftype SDH-Action-HLA [hierarchy name action precond-var-set precond-hlas] :as this
  SDH-HLA
    (active-var-set []  (apply clojure.set/union (map active-var-set precond-hlas)))
    (leaf-var-set   []  (apply clojure.set/union (map leaf-var-set precond-hlas)))
    (greedy?        [s v av] 
      (or (every? #(and (satisfied? % s) (or (active? %) (not (av (:var %))))) precond-hlas)
          (some #(greedy? % s v av) (util/make-safe (seq (filter #(contains? (leaf-var-set %) v) precond-hlas))))
          ))
    (do-refinement  [s v av lv]
      (if (every? #(and (satisfied? % s) (or (active? %) (not (av (:var %))))) precond-hlas) 
          (do (println "GREED2") [[[action] nil]])
        (let [possible-vals  (filter #(contains? (leaf-var-set %) v) precond-hlas)
              [deep shallow] (util/separate active? possible-vals)
              val-options    (or (and (:greedy-optimization? hierarchy) 
                                      (when-first [x (filter #(greedy? % s v av) deep)] [x])) 
                                 (seq deep) 
                                 (seq shallow))]
;          (println "refining at " v "with options" val-options)
            (assert (seq val-options))
            (assert (<= (count shallow) 1))
        
            (for [precond-hla val-options
                  [prefix remaining] (do-refinement precond-hla s v av lv)]
              [prefix 
               (let [new-precond-hlas
                      (for [hla precond-hlas]
                        (if (identical? hla precond-hla) remaining hla))]
                 (SDH-Action-HLA. hierarchy
                   [:!A* (env/action-name action) (map env/action-name new-precond-hlas)]
                   action precond-var-set new-precond-hlas))]))))
  env/Action
    (action-name     [] name)
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] precond-var-set)
  hierarchy/HighLevelAction
    (immediate-refinements- [s]
      (if (every? #(satisfied? % s) precond-hlas) (do (println "gREED!") [[action]])
        (let [var-actives (active-var-set this)
              var-leaves  (leaf-var-set this)
              var-options (clojure.set/difference var-leaves var-actives)]
          (if (empty? var-options)
              (println "Dead end!")
            (for [[prefix remaining]
                  (do-refinement this s (util/first-maximal-element (:var-levels hierarchy) var-options)
                                 var-actives var-leaves)]
              (if remaining (concat prefix [remaining]) prefix))))))
    (cycle-level-           [s] nil))

(defn- make-action-hla [hierarchy action]
  (let [effect-var (key (util/safe-singleton (:effect-map action)))
        reduced-em (dissoc (:precond-map action) effect-var)]
    (if (empty? reduced-em)
        action
      (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action
                      ((:ancestor-var-set hierarchy) effect-var)
                      (for [[pvar pval] reduced-em]
                        (make-leaf-precond-hla hierarchy pvar pval))))))

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








(comment
  
  

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
                    (make-interleaving-hla hierarchy (select-keys pc-map pc-batch)))
              (let [pc (util/safe-singleton pc-batch)]
                (make-precond-hla hierarchy pc (get pc-map pc))))))
        [action])])
    (cycle-level-           [s] nil))

(defn- make-action-hla [hierarchy action]
  (let [effect-var (key (util/safe-singleton (:effect-map action)))]
    (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action effect-var
                    ((:ancestor-var-set hierarchy) effect-var))))


  )