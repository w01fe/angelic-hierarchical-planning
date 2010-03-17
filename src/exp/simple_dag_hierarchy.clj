(ns simple-dag-hierarchy
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs] [graphviz :as gv]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
;  (:import [java.util HashMap HashSet IdentityHashMap])
  )




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *vars* nil)
(def *var-val-sets* nil)  ; Map from var name to set of all vals.
(def *var-levels*   nil)  ; Map from var name to index in topological sort (0 is src, +n is sink)
(def *extended-dtgs* nil) ; Map from var to map from prev val to map from post val to list of actions.
(def *simple-dtgs* nil)   ; Map from var to edge list.
(def *greedy-optimization?* true)

;; Memoized partial computations to speed up acylic edge generation.
(def #^HashMap *forward-reachability-cache* nil)
(def #^HashMap *backward-reachability-cache* nil)

(defn forward-reachable-nodes-and-necessary-predecessors [var-name from-val]
  (util/cache-with *forward-reachability-cache* [var-name from-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (util/safe-get *simple-dtgs* var-name) from-val)))

(defn backward-reachable-nodes-and-necessary-predecessors [var-name to-val]
  (util/cache-with *backward-reachability-cache* [var-name to-val]
    (graphs/compute-reachable-nodes-and-necessary-predecessors
     (map reverse (util/safe-get *simple-dtgs* var-name)) to-val)))

(defn get-possibly-acyclic-edges
  "Return a list of edges, where those provably on no acyclic s-t path have been eliminated.
   Do so in polynomial time, possibly missing some always-cyclic edges."  
  [var from-val to-val]
  (let [forward-sets  (forward-reachable-nodes-and-necessary-predecessors var from-val)
        backward-sets (backward-reachable-nodes-and-necessary-predecessors var to-val)]
    (filter
     (fn [[a b]]
       (let [f (forward-sets a)
             b (backward-sets b)]
         (and f b (empty? (clojure.set/intersection f b)))))
     (util/safe-get *simple-dtgs* var))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol SAS-Induced-Action
  (precond-var-set [a])
  (effect-sets     [a])
  (pre-ref-pairs   [a])
  (compile-hla     [a retain-type-set])
  (extend-hla!     [a init-sets par-effect-sets])
  (hla-type        [a]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
;     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a))) ;?
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))
     :pre-ref-pairs   (fn [a] (throw (UnsupportedOperationException.)))
     :compile-hla     (fn [a retain-type-set] a)
     :extend-hla!     (fn [a init-sets par-effect-sets] a)
     :hla-type        (fn [a] (throw (UnsupportedOperationException.)))})




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; VV HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare get-current-action-hla extend-action-hla!)

(declare extend-vv-hla!)
;; TODO: special treatment for "free"  vars without self-loops.
;; TODO: try harder to avoid cycles, e.eg. in logistics / multi-taxi domain. 
;; Either all-paths or blacklist approaches will work. 

(defn vv-hla-name [var src-val dst-val] [:!VV src-val dst-val])

; successor-map is a map from dst-val to list of [ap-hla next-vv-hla] pairs. 
(deftype SAS-VV-HLA  [var src-val dst-val src?-atom dirty?-atom init-sets-atom par-effects-atom precond-vars-atom effect-sets-atom successor-map-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
    (pre-ref-pairs   [] (if (= src-val dst-val) [[{} []]] 
                            (for [vs (vals @successor-map-atom), v vs] [{} v])))
    (compile-hla     [retain-type-set] (if (= src-val dst-val) [] (default-compile-hla this retain-type-set)))
    (hla-type        [] (type this))
    (extend-hla!     [init-sets par-effect-sets] (extend-vv-hla! this init-sets par-effect-sets true))
  env/Action
    (action-name [] (vv-hla-name var src-val dst-val))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] @precond-vars-atom)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] (if (= src-val dst-val) [[]] (apply concat (vals @successor-map-atom))))
    (cycle-level-           [s] nil))

(defn get-current-vv-hla [var src-val dst-val]
  (util/cache-with *hla-cache* (vv-hla-name var src-val dst-val)
    (if (= src-val dst-val)
      (SAS-VV-HLA var src-val dst-val (atom true) (atom false) (atom *var-val-sets*) (atom {}) (atom #{var}) (atom {}) (atom {}))      
      (SAS-VV-HLA var src-val dst-val (atom false) (atom false) (atom {})            (atom {}) (atom #{var}) (atom no-outcomes) (atom {})))))

(declare extend-vv-hla-edge!)

(defn add-new-vv-edge! [var dst-val [s t]]
  (let [sn (get-current-vv-hla var s dst-val)]
    (when-not (contains? @(:successor-map-atom sn) t)
      (when (seq @(:init-sets-atom sn)) #_(println "Warning: adding outgoing edge! (sas_hierarchy_induction)" [s t]))
      (swap! (:successor-map-atom sn) assoc t
             (doall (for [a (util/safe-get-in *extended-dtgs* [var s t])] 
                      [(get-current-action-hla a) (get-current-vv-hla var t dst-val)]))))))


;; TODO: take "at most 1 free action" constraint into account. 
(defn designate-vv-hla-src! [hla]
  (let [{:keys [var src-val dst-val src?-atom]} hla
        edges    (get-possibly-acyclic-edges var src-val dst-val)
        any-new? (some identity (doall (map #(add-new-vv-edge! var dst-val %) edges)))]
;    (println "adding edges" edges "for" src-val "-->" dst-val)
;    (gv/graphviz-el edges)
    (util/assert-is (or (seq edges) (= src-val dst-val)) "%s" [src-val dst-val])
    (reset! src?-atom true)
    (when any-new? 
      (doseq [s (distinct (map first edges))]
        (reset! (:dirty?-atom (get-current-vv-hla var s dst-val)) true)))))


(defn extend-vv-hla! 
  "Extend this HLA to cover new init-sets, as needed. src? indicates whether this value can be a source from a descendent."
  [hla init-sets par-effect-sets src?]
  (assert (not (contains? (apply clojure.set/union (vals init-sets)) no-effect-val)))
  (let [{:keys [var src-val dst-val src?-atom dirty?-atom init-sets-atom par-effects-atom precond-vars-atom successor-map-atom]} hla]
;    (println "Extend" (:var hla) (:src-val hla) (:dst-val hla) new-inits? (count @successor-map-atom))
    (util/assert-is (= (util/safe-get init-sets var) #{src-val}))
    (when (and src? (not @src?-atom)) (designate-vv-hla-src! hla))
    (when (or (not= (select-keys @init-sets-atom @precond-vars-atom)
                    (select-keys (swap! init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))
              (not= (select-keys @par-effects-atom @precond-vars-atom)
                    (select-keys (swap! par-effects-atom #(merge-with clojure.set/union % par-effect-sets)) @precond-vars-atom))
              @dirty?-atom) 
      (reset! dirty?-atom false)
      (doseq [es (vals @successor-map-atom), e es] (extend-vv-hla-edge! hla e @init-sets-atom @par-effects-atom)))))

;; TODO: make sure this is general enough handling of precond sets.
(defn extend-vv-hla-edge! 
  "Extend this VV-HLA edge to cover new init-sets, as needed."
  [hla [a next-vv-hla] init-sets par-effect-sets]
  (assert (not (= (:src-val hla) (:dst-val hla))))
;  (println "Start extend" (:src-val hla) (:dst-val hla) "via" (:src-val next-vv-hla))
  (extend-hla! a init-sets par-effect-sets)
;  (println (env/action-name hla) init-sets (effect-sets hla) (effect-sets a) (effect-sets next-vv-hla))
  (extend-vv-hla! next-vv-hla (apply-effect-set-map init-sets (effect-sets a)) par-effect-sets false)
  (when-not (= (effect-sets next-vv-hla) no-outcomes)
;    (println "Warning: no effect sets ... cyclic dTG?")
;    (throw (RuntimeException. (str (:src-val hla) (:dst-val hla) (:src-val next-vv-hla))))
    
    (swap! (:precond-vars-atom hla) clojure.set/union       (precond-var-set a) (precond-var-set next-vv-hla))
    (swap! (:effect-sets-atom hla)  disjoin-effect-set-maps (sequence-effect-set-maps (effect-sets a) (effect-sets next-vv-hla)))
    (util/assert-is (= (get @(:effect-sets-atom hla) (:var hla)) #{(:dst-val hla)}) "%s" [(env/action-name hla)])
;    (println "Finish extend" (:src-val hla) (:dst-val hla) "via" (:src-val next-vv-hla))   
    ))






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
(deftype SAS-Precond-Set-HLA [precond-map ordered-preconds ref-atom] :as this
  SAS-Induced-Action
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
  (SAS-Precond-Set-HLA 
   precond-map
   (doall (map (partial apply make-precond-hla) (sort-by (comp - *var-levels* key) precond-map)))
   (atom :dummy)))

(defn trivially-satisfied-precond-set? [a s]
  (if (= (type a) ::SAS-Compiled-HLA) (recur (:orig-hla a) s)
      (and (= (type a) ::SAS-Precond-Set-HLA)
           (every? (fn [p] (= (env/get-var s (:var p)) (:dst-val p)))
                   (:ordered-preconds a)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An action.  
;; TODO: think about splitting this based on which var it's being used for.

(defn action-hla-name [action] [:!A (env/action-name action)])

(deftype SAS-Action-HLA [action precond-set-hla]; init-sets-atom precond-vars-atom effect-sets-atom] 
                                :as this
  SAS-Induced-Action
    (precond-var-set [] (clojure.set/union (precond-var-set precond-set-hla) (util/keyset (:precond-map action))))
    (effect-sets     [] (sequence-effect-set-maps (effect-sets precond-set-hla) (util/map-vals (fn [x] #{x}) (:effect-map action))))
    (pre-ref-pairs   [] [[{} [precond-set-hla action]]])
    (compile-hla     [retain-type-set] (default-compile-hla this retain-type-set))
    (hla-type        [] (type this))    
    (extend-hla!     [init-sets par-effect-sets] (extend-hla! precond-set-hla init-sets par-effect-sets))
  env/Action
    (action-name     [] (action-hla-name action))
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [[precond-set-hla action]])
    (cycle-level-           [s] nil))

(defn get-current-action-hla [action]
  (let [preconds     (:precond-map action)]
    (util/cache-with *hla-cache* (action-hla-name action)
      (SAS-Action-HLA action (make-precond-set-hla preconds)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interleaving HLA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-interleaving-hla-refinement)

(deftype SAS-Interleaving-HLA [refinements shared-var-set] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union (map precond-var-set (apply concat refinements))))
    (effect-sets     [] (throw (UnsupportedOperationException.)))
    (pre-ref-pairs   [] (throw (UnsupportedOperationException.)))
    (compile-hla     [retain-type-set]
;      (println "interleaved compile" (map #(map env/action-name %) refinements))
      (SAS-Interleaving-HLA. (vec (map #(compile-refinement % (conj retain-type-set ::SAS-Precond-Set-HLA)) refinements)) shared-var-set))
    (hla-type        [] (type this))
    (extend-hla!     [init-sets par-effect-sets] (throw (UnsupportedOperationException.)))
  env/Action
    (action-name     [] [:!I (map #(map env/action-name %) refinements) shared-var-set])
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s]
      (let [[stalled-refs rest-refs] (split-with #(= (hla-type (first %)) ::SAS-Precond-Set-HLA) refinements)]
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
  (SAS-Interleaving-HLA (vec refinements) shared-var-set))

;; Greedily pull irrelevant actions out, until we get to a normalized HLA
(defn make-interleaving-hla-refinement [pre-actions refinements shared-var-set]  
  (loop [in-refinements refinements, out-refinements [], pre-actions pre-actions]
    (if-let [[f & r] (seq in-refinements)]
      (let [[front back] (split-with #(or (empty? (clojure.set/intersection shared-var-set (precond-var-set %)))
                                          (env/primitive? %)) f)]
        (recur r (if (seq back) (conj out-refinements back) out-refinements) (concat pre-actions front)))
      (concat pre-actions (when (seq out-refinements) [(make-interleaving-hla out-refinements shared-var-set)])))))
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top Level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-simple-dag-hierarchy [sas-problem]
  (assert (graphs/dag? (sas-analysis/standard-causal-graph sas-problem)))
  (assert (sas-analysis/homogenous? sas-problem))
  (let [bla 'bla]
    (binding [bla 'bla]
      (hierarchy/SimpleHierarchicalEnv sas-problem 
        [(make-action-hla
          (util/safe-singleton 
           (get-in *extended-dtgs* 
             [sas/goal-var-name sas/goal-false-val sas/goal-true-val])))]))))




