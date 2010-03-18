(ns simple-dag-hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  (:import [java.util HashMap])
  )




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: in purely static analysis, either cannot prune source vals, or must 
;; split HLAs.  Here, this amounts to, more or less, just removing outgoing arcs from goal.
;; We can just do this implicitly, and forget about real acyclic stuff in this version.
; TODO: (could do better, e.g., for line DTGs)



(declare make-action-hla)

(deftype Simple-Tree-Hierarchy 
  [sas-problem 
   predecessor-var-set
   ancestor-var-set
   var-levels
   dtg-to       ; fn from var & dst-val to map from cur-val to map from nxt-val to actions
   cycle-to     ; from from var & dst-val to map from cur-val to bool, if can cycle from cur-val
   greedy-optimization?])

(defn make-simple-tree-hierarchy [sas-problem]
  (let [causal-graph (sas-analysis/standard-causal-graph sas-problem)
        pred-var-set (util/map-vals (comp set #(map first %))
                                    (util/unsorted-group-by second causal-graph)) 
        dtgs         (sas-analysis/domain-transition-graphs sas-problem)
        dtg-to       (fn [var dst-val] (util/safe-get dtgs var))]

    (assert (graphs/inverted-tree-reducible? causal-graph))
    (assert (sas-analysis/homogenous? sas-problem))    

    (hierarchy/SimpleHierarchicalEnv sas-problem 
      [(make-action-hla 
        (Simple-Tree-Hierarchy
         sas-problem
         pred-var-set
         (util/memoized-fn ancestor-var-set [var]
           (conj (--> (util/safe-get pred-var-set var)
                      (map ancestor-var-set)
                      (apply clojure.set/union))
                 var))
         (graphs/topological-sort-indices causal-graph)
         dtg-to
         (util/memoized-fn cycle-to [var dst-val]
           (let [dtg (dtg-to var dst-val)
                 tsi (graphs/topological-sort-indices
                      (for [[pval emap] dtg, eval (keys emap)
                            :when (not (= pval dst-val))] 
                        [pval eval]))]
             (reduce (fn [m next-vars]
                       (if (> (count next-vars) 1)
                           (reduce #(assoc %1 %2 true) m next-vars)
                         (let [v (util/safe-singleton next-vars)]
                           (assoc m v (some m (keys (get dtg v)))))))
                     {} (reverse (map #(map key %) (vals (util/group-by val tsi)))))))
         false)
        (->> dtgs
             (get-in [sas/goal-var-name sas/goal-false-val sas/goal-true-val])
             util/safe-singleton))])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defprotocol SDH-HLA
  (precond-var-set [a])
  (effect-sets     [a])
  (pre-ref-pairs   [a])
  (compile-hla     [a retain-type-set])
  (extend-hla!     [a init-sets par-effect-sets])
  (hla-type        [a]))

(extend ::env/FactoredPrimitive
  SDH-HLA
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
;     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a))) ;?
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))
     :pre-ref-pairs   (fn [a] (throw (UnsupportedOperationException.)))
     :compile-hla     (fn [a retain-type-set] a)
     :extend-hla!     (fn [a init-sets par-effect-sets] a)
     :hla-type        (fn [a] (throw (UnsupportedOperationException.)))})




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precond HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype SDH-Precond-HLA  [hierarchy name var dst-val dtg precond-var-set cycle-level] :as this
  SDH-HLA
  env/Action
    (action-name [] name)
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] precond-var-set)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] 
      (let [cur-val (env/get-var s var)])
        (if (= cur-val dst-val)
            [[]]
          (for [[as (vals (get dtg cur-val)), action as]]
            [(make-action-hla action) this])))
    (cycle-level-           [s] cycle-level))

(defn make-precond-hla [hierarchy var dst-val]
  (SCH-Precond-HLA hierarchy [:!PRECOND var dst-val] var dst-val 
                   (--> hierarchy :dtg-to var dst-val)
                   (--> hierarchy :ancestor-vars-set var)
                   (when (--> hierarchy :cycle-to var dst-val) 
                     (--> hierarchy :var-levels var))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;[sas-problem predecessor-var-set ancestor-var-set var-levels dtg-to cycle-to greedy-optimization?]

(deftype SDH-Action-HLA [hierarchy name action precond-hlas precond-var-set]
  SDH-HLA
  env/Action
    (action-name     [] name)
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] precond-var-set)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] 
      (if (<= (count precond-hlas) 1)
          [(concat precond-hlas [action])]
        ***))
    (cycle-level-           [s] nil))

(defn make-action-hla [hierarchy action]
  (let [effect-var (key (util/safe-singleton (:effect-map action)))]
    (SDH-Action-HLA hierarchy [:!A (env/action-name action)] action 
                    (for [[var val] (:precond-map action)
                          :when (not (= var effect-var))] 
                      (make-precond-hla hierarchy var val))
                    (--> hierarchy :ancestor-vars-set effect-var))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precondition Set Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ; This assumes no value-added needed:

;; Idea: graph where a, b connected if precond sets intersect.
 ; Arc is a->b if a superset of b, bid. if no containment. 
 ; any Topological order gives proper structure? (SCC-graph must be a tree!)
; This loses on things like a -> b -> c , d -> c where we should get orering of a/b.

;; TODO: recursively do these sets, somehow.


(defn compute-precond-var-sets [init-sets par-effect-sets ordered-preconds]
  (loop [init-sets init-sets, ordered-preconds ordered-preconds, ret []]
    (if-let [[f & r] (seq ordered-preconds)]        
        (do (extend-hla! f init-sets par-effect-sets)
            (recur (apply-effect-set-map init-sets (effect-sets f)) 
                   r
                   (conj ret [f (precond-var-set f)])))
      ret)))

(defn compute-interference-graph [preconds-and-var-sets]
  (concat
   (for [g preconds-and-var-sets] [::ROOT g])
   (for [[p1 s1 :as g1] preconds-and-var-sets, [p2 s2 :as g2] preconds-and-var-sets
         :when (and (not (empty? (clojure.set/intersection s1 s2)))
                    (not (util/superset? s2 s1)))]
     [g1 g2])))

(defn compute-topo-map [init-sets par-effect-sets ordered-preconds]
  (graphs/topological-sort-indices
   (compute-interference-graph
    (compute-precond-var-sets init-sets par-effect-sets ordered-preconds))))

;; TODO: To properly know which vars to fiddle, must be able to separate direct effects from transitive ones.  

;; TODO: also must remember prec/effect dichotomy. 

(declare extend-precond-set-hla! make-interleaving-hla)
;; Preconds are ordered, max-level (deepest) first.
(deftype SDH-Precond-Set-HLA [precond-map ordered-preconds ref-atom] :as this
  SDH-HLA
    (precond-var-set [] (apply clojure.set/union        (map precond-var-set ordered-preconds)))
    (effect-sets     [] (apply sequence-effect-set-maps (map effect-sets ordered-preconds)))
    (pre-ref-pairs   [] [[{} @ref-atom]])
    (compile-hla     [retain-type-set] (default-compile-hla this retain-type-set))
    (hla-type        [] (type this))
    (extend-hla!     [init-sets par-effect-sets] 
      (extend-precond-set-hla! this init-sets par-effect-sets))
  env/Action
    (action-name [] [:ps (System/identityHashCode this)])
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [@ref-atom])
    (cycle-level-           [s] nil))

;; For now, punt in several ways, only look for independent chunks, ...
; Broken out so it can access bound vars.
(defn extend-precond-set-hla! [hla init-sets par-effect-sets]  
  (let [{:keys [ordered-preconds ref-atom]} hla
        topo-map (compute-topo-map init-sets par-effect-sets ordered-preconds)
        chunks   (map #(map key %) (vals (util/group-by val topo-map)))]
    (assert (= (first chunks) [::ROOT]))
;    (println (map #(map (comp env/action-name first) %) (next chunks)))
    (reset! ref-atom 
      (doall
       (for [chunk (next chunks)] 
         (if (util/singleton? chunk)
           (ffirst chunk)
           (let [all-vars (apply concat (map second chunk))
                 bad-vars (util/keyset (util/filter-map #(> (val %) 1) (util/frequencies all-vars)))
                 par-effect-sets (select-keys *var-val-sets* bad-vars)]
             (println "Interleaving HLAs with common ground:" bad-vars par-effect-sets)
             (doseq [[hla] chunk] (extend-hla! hla {} par-effect-sets))
             (assert (= (set all-vars) (set (apply concat (map second chunk)))))
             (make-interleaving-hla (map (comp vector first) chunk) bad-vars))))))))

(defn make-precond-set-hla [precond-map] 
  (SDH-Precond-Set-HLA 
   precond-map
   (doall (map (partial apply make-precond-hla) (sort-by (comp - *var-levels* key) precond-map)))
   (atom :dummy)))

(defn trivially-satisfied-precond-set? [a s]
  (if (= (type a) ::SDH-Compiled-HLA) (recur (:orig-hla a) s)
      (and (= (type a) ::SDH-Precond-Set-HLA)
           (every? (fn [p] (= (env/get-var s (:var p)) (:dst-val p)))
                   (:ordered-preconds a)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interleaving HLA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-interleaving-hla-refinement)

(deftype SDH-Interleaving-HLA [refinements shared-var-set] :as this
  SDH-HLA
    (precond-var-set [] (apply clojure.set/union (map precond-var-set (apply concat refinements))))
    (effect-sets     [] (throw (UnsupportedOperationException.)))
    (pre-ref-pairs   [] (throw (UnsupportedOperationException.)))
    (compile-hla     [retain-type-set]
;      (println "interleaved compile" (map #(map env/action-name %) refinements))
      (SDH-Interleaving-HLA. (vec (map #(compile-refinement % (conj retain-type-set ::SDH-Precond-Set-HLA)) refinements)) shared-var-set))
    (hla-type        [] (type this))
    (extend-hla!     [init-sets par-effect-sets] (throw (UnsupportedOperationException.)))
  env/Action
    (action-name     [] [:!I (map #(map env/action-name %) refinements) shared-var-set])
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s]
      (let [[stalled-refs rest-refs] (split-with #(= (hla-type (first %)) ::SDH-Precond-Set-HLA) refinements)]
;        (println "\n\n" s "\n" (map (comp env/action-name first) refinements))
;        (println (map count [stalled-refs rest-refs]))
;        (println (map #(map type %) rest-refs))
        (if-let [[target-ref & more-refs] (seq rest-refs)]
            (let [[first-a & rest-a] target-ref]
              (for [ref (hierarchy/immediate-refinements first-a s)]
                (make-interleaving-hla-refinement nil
                  (concat stalled-refs [(concat ref rest-a)] more-refs)
                  shared-var-set)))
           ;; Interesting stuff here ... all refinements are blocked at precond set HLAs.
           ;; First placeholder (not complete or smart): just pick one to do completely, no interleaving.
          (if (and *greedy-optimization?* (some #(trivially-satisfied-precond-set? (first %) s) refinements))
              (do ;(println "GREEDY") ;; TODO: is this the best place?
                [(make-interleaving-hla-refinement
                  [] ; (for [ref refinements :let [f (first ref)] :when (trivially-satisfied-precond-set? f s)] f)
                  (for [ref refinements]
                    (if (trivially-satisfied-precond-set? (first ref) s) (next ref) ref))
                  shared-var-set)])
            (for [i (range (count refinements))
                  :let [[f & r] (nth refinements i)]]
              (make-interleaving-hla-refinement [f]               
                (concat (subvec refinements 0 i) [r] (subvec refinements (inc i)))
                shared-var-set))))))
    (cycle-level-           [s] nil))

(defn make-interleaving-hla [refinements shared-var-set]
  (SDH-Interleaving-HLA (vec refinements) shared-var-set))

;; Greedily pull irrelevant actions out, until we get to a normalized HLA
(defn make-interleaving-hla-refinement [pre-actions refinements shared-var-set]  
  (loop [in-refinements refinements, out-refinements [], pre-actions pre-actions]
    (if-let [[f & r] (seq in-refinements)]
      (let [[front back] (split-with #(or (empty? (clojure.set/intersection shared-var-set (precond-var-set %)))
                                          (env/primitive? %)) f)]
        (recur r (if (seq back) (conj out-refinements back) out-refinements) (concat pre-actions front)))
      (concat pre-actions (when (seq out-refinements) [(make-interleaving-hla out-refinements shared-var-set)])))))
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top Level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






