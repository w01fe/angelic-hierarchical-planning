(ns exp.sas-hierarchy-induction
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  (:import [java.util HashMap HashSet]))


;; Right now, this is only for DAGs. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def no-effect-val ::NO-EFFECT)
(def no-effect-set #{no-effect-val})
(def no-outcomes ::NO-EXIT)

(defn disjoin-effect-set-maps 
  ([] {})
  ([m] m)
  ([m1 m2]
     (cond (= m1 no-outcomes) m2
           (= m2 no-outcomes) m1
           :else (util/map-map 
                  (fn [k] [k (clojure.set/union (get m1 k no-effect-set) (get m2 k no-effect-set))])
                  (distinct (concat (keys m1) (keys m2))))))
  ([m1 m2 & maps]
     (reduce disjoin-effect-set-maps m1 (cons m2 maps))))

(defn sequence-effect-set-maps 
  ([] {})
  ([m] m)
  ([m1 m2]
      (reduce (fn [m [ek evs]]
                (let [ovs (get m1 no-effect-set)]
                  (assoc m ek (if (contains? evs no-effect-val) (clojure.set/union ovs (disj evs no-effect-val)) evs))))
              m1 m2))
  ([m1 m2 & maps]
     (reduce sequence-effect-set-maps m1 (cons m2 maps))))

(defn apply-effect-set-map [init-sets effect-set-map]
  (reduce (fn [m [ek evs]]
            (let [ovs (util/safe-get init-sets ek)]
              (assoc m ek (if (contains? evs no-effect-val) (clojure.set/union ovs (disj evs no-effect-val)) evs))))
          init-sets effect-set-map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *vars* nil)
(def *var-val-sets* nil)  ; Map from var name to set of all vals.
(def *var-levels*   nil)  ; Map from var name to index in topological sort (0 is src, +n is sink)
(def *extended-dtgs* nil) ; Map from var to map from prev val to map from post val to list of actions.
(def *simple-dtgs* nil)   ; Map from var to edge list.
(def #^HashMap *hla-cache* nil) ; a map from [action-name] to map from init-sets to action.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Difference from precond-var-set and precondition-context is for primitives (?)
;; Compile-Hla may return an HLA, or a single ref.
; extend-hla-par! extends hla to handle any other action setting these effects in-between accesses to these vars.
(defprotocol SAS-Induced-Action
  (precond-var-set [a])
;  (initial-sets    [a])
  (effect-sets     [a])
  (pre-ref-pairs   [a])
  (compile-hla     [a])
  (extend-hla!     [a init-sets par-effect-sets]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
;     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a))) ;?
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))
     :pre-ref-pairs   (fn [a] (throw (UnsupportedOperationException.)))
     :compile-hla     (fn [a] a)
     :extend-hla!     (fn [a init-sets par-effect-sets] a)})

(deftype SAS-Compiled-HLA [name precond-vars effects refinements-and-preconditions ref-generator] :as this
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (effect-sets     [] effects)
    (pre-ref-pairs   [] refinements-and-preconditions)
    (compile-hla     [] this)
    (extend-hla!     [init-sets par-effect-sets] (throw (UnsupportedOperationException.)))
  env/Action
    (action-name [] name)
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] precond-vars)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] (ref-generator s))
    (cycle-level-           [s] nil))

(defn make-ref-generator [refinements-and-preconditions]
  (if (every? empty? (map first refinements-and-preconditions))
      (let [refs (map second refinements-and-preconditions)]
        (constantly refs))
    (fn [s]
      (for [[pre-pairs ref] refinements-and-preconditions, 
            :when (every? (fn [[var val]] (= val (env/get-var s var))) pre-pairs)]
        ref))))

(defn make-compiled-hla [name precond-vars effects pre-ref-pairs]
  (SAS-Compiled-HLA name precond-vars effects pre-ref-pairs (make-ref-generator pre-ref-pairs)))

(defn compile-refinement [ref]
  (loop [ref ref, compiled []]
    (if-let [[f & r] (seq ref)]
      (let [cf (compile-hla f)]
        (if (or (nil? cf) (sequential? cf))
            (recur r (into compiled cf))
          (recur r (conj compiled cf))))
      compiled)))


(defn default-compile-hla-noflatten [hla]
  (make-compiled-hla (env/action-name hla) (precond-var-set hla) (effect-sets hla) 
    (for [[p r] (pre-ref-pairs hla)] [p (compile-refinement r)])))

(defn default-compile-hla [hla]
  (let [pr (pre-ref-pairs hla)]
    (if (and (util/singleton? pr) (empty? (ffirst pr)))
        (compile-refinement (second (first pr)))
      (default-compile-hla-noflatten hla))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; VV HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare get-current-action-hla extend-action-hla!)

(declare extend-vv-hla!)
;; TODO: special treatment for "free"  vars without self-loops.
;; TODO: try harder to avoid cycles, e.eg. in logistics / multi-taxi domain. 
;; TODO**: look at "meeting" conditions, e.g., in logistics, only dropoff at non-goal if other vehicle waiting ?
;; Either all-paths or blacklist approaches will work. 

(defn vv-hla-name [var src-val dst-val] [:!VV src-val dst-val])

; successor-map is a map from dst-val to list of [ap-hla next-vv-hla] pairs. 
(deftype SAS-VV-HLA  [var src-val dst-val src?-atom dirty?-atom init-sets-atom par-effects-atom precond-vars-atom effect-sets-atom successor-map-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
    (pre-ref-pairs   [] (if (= src-val dst-val) [[{} []]] 
                            (for [vs (vals @successor-map-atom), v vs] [{} v])))
    (compile-hla     [] (if (= src-val dst-val) [] (default-compile-hla #_-noflatten this)))
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
      (when (seq @(:init-sets-atom sn)) (println "Warning: adding outgoing edge! (sas_hierarchy_induction)" [s t]))
      (swap! (:successor-map-atom sn) assoc t
             (doall (for [a (util/safe-get-in *extended-dtgs* [var s t])] 
                      [(get-current-action-hla a) (get-current-vv-hla var t dst-val)]))))))


(defn designate-vv-hla-src! [hla]
  (let [{:keys [var src-val dst-val src?-atom]} hla
        edges    (graphs/find-acyclic-edges (util/safe-get *simple-dtgs* var) [src-val] [dst-val])
        any-new? (some identity (doall (map #(add-new-vv-edge! var dst-val %) edges)))]
;    (println "adding edges" edges)
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
  (extend-hla! a init-sets par-effect-sets)
;  (println (env/action-name hla) init-sets (effect-sets hla) (effect-sets a) (effect-sets next-vv-hla))
  (extend-vv-hla! next-vv-hla (apply-effect-set-map init-sets (effect-sets a)) par-effect-sets false)

  (swap! (:precond-vars-atom hla) clojure.set/union       (precond-var-set a) (precond-var-set next-vv-hla))
  (swap! (:effect-sets-atom hla)  disjoin-effect-set-maps (sequence-effect-set-maps (effect-sets a) (effect-sets next-vv-hla)))
  (util/assert-is (= (get @(:effect-sets-atom hla) (:var hla)) #{(:dst-val hla)}) "%s" [(env/action-name hla)]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precondition Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each precond HLA is not cached, and is owned by a particular action.
;; It just aggregates sets of src vv-hla nodes, more or less.
;; src-map-atom maps from src vals to sas-vv-hla instances.  Init-sets describes current init-sets.

(deftype SAS-Precond-HLA [var dst-val src-map-atom par-effects-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union       (map precond-var-set (vals @src-map-atom))))
    (effect-sets     [] (apply disjoin-effect-set-maps @par-effects-atom (map effect-sets     (vals @src-map-atom))))
    (pre-ref-pairs   [] (if (util/singleton? @src-map-atom) 
                            [[{} [(first (vals @src-map-atom))]]]
                          (for [[k v] @src-map-atom] [{var k} [v]])))
    (compile-hla     [] (default-compile-hla this))
    (extend-hla!     [init-sets par-effect-sets]
      (assert (every? set? (vals init-sets)))
      (assert (every? set? (vals par-effect-sets)))
      (assert (not (contains? (apply clojure.set/union (vals init-sets)) no-effect-val)))
      (if (contains? par-effect-sets var)
          (do (println "RAB")
              (swap! par-effects-atom #(merge-with clojure.set/union par-effect-sets %)) 
              (extend-hla! this (merge-with clojure.set/union init-sets (apply-effect-set-map init-sets par-effect-sets)) {}))
        (let [par-effects? (seq (clojure.set/intersection (util/keyset par-effect-sets) (precond-var-set this)))]
          (println "OTH" );(set (get init-sets var)) (when par-effects? (keys @src-map-atom)))
;          (println (util/map-vals type init-sets))
          (assert (not (contains? (set (get init-sets var)) no-effect-val)))
          (doseq [src-val (util/union-coll (set (get init-sets var)) (when par-effects? (keys @src-map-atom)))]
            (util/assert-is  (not= src-val no-effect-val))
            (when-not (contains? @src-map-atom src-val)
              (swap! src-map-atom assoc src-val (get-current-vv-hla var src-val dst-val)))
            (extend-hla! (util/safe-get @src-map-atom src-val) (assoc init-sets var #{src-val}) (if par-effects? par-effect-sets {}))))))
  env/Action
    (action-name [] [:precond var dst-val (System/identityHashCode this)])
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [[(util/safe-get @src-map-atom (env/get-var s var))]])
    (cycle-level-           [s] nil))

(defn make-precond-hla [var dst-val] 
  (SAS-Precond-HLA var dst-val (atom {}) (atom {})))



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
(deftype SAS-Precond-Set-HLA [ordered-preconds ref-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union        (map precond-var-set ordered-preconds)))
    (effect-sets     [] (apply sequence-effect-set-maps (map effect-sets ordered-preconds)))
    (pre-ref-pairs   [] [[{} @ref-atom]])
    (compile-hla     [] (default-compile-hla this))
    (extend-hla!     [init-sets par-effect-sets] ;; For now, punt in several ways, only look for independent chunks, ...
      (extend-precond-set-hla! this init-sets par-effect-sets))
  env/Action
    (action-name [] [:ps (System/identityHashCode this)])
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [@ref-atom])
    (cycle-level-           [s] nil))

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
             (println "BLADSFLASDFL" bad-vars par-effect-sets)
             (doseq [[hla] chunk] (extend-hla! hla {} par-effect-sets))
             (assert (= (set all-vars) (set (apply concat (map second chunk)))))
             (make-interleaving-hla (map (comp vector first) chunk) bad-vars))))))))

(defn make-precond-set-hla [precond-map] 
  (SAS-Precond-Set-HLA (map (partial apply make-precond-hla) (sort-by (comp - *var-levels* key) precond-map))
                       (atom :dummy)))


; (loop [init-sets init-sets, ordered-preconds ordered-preconds, used-vars #{}]
;        (when-let [[f & r] (seq ordered-preconds)]        
;          (extend-hla! f init-sets)
;          (util/assert-is (or (contains? used-vars (:var f))
;                              (empty? (clojure.set/intersection used-vars (precond-var-set f))))
;                          "%s" [used-vars (:var f) (precond-var-set f)])
;          (recur (apply-effect-set-map init-sets (effect-sets f)) 
;                 r
;                 (clojure.set/union used-vars (precond-var-set f) (util/keyset (effect-sets f))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

0;; An action.  
;; TODO: think about splitting this based on which var it's being used for.
;; TODO: make fancier.


(defn action-hla-name [action] [:!A (env/action-name action)])

(deftype SAS-Action-HLA [action precond-set-hla]; init-sets-atom precond-vars-atom effect-sets-atom] 
                                :as this
  SAS-Induced-Action
    (precond-var-set [] (clojure.set/union (precond-var-set precond-set-hla) (util/keyset (:precond-map action))))
    (effect-sets     [] (sequence-effect-set-maps (effect-sets precond-set-hla) (util/map-vals (fn [x] #{x}) (:effect-map action))))
    (pre-ref-pairs   [] [[{} [precond-set-hla action]]])
    (compile-hla     [] (default-compile-hla this))
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
      (SAS-Action-HLA action (make-precond-set-hla preconds))))); (atom {}) (atom (util/keyset preconds)) (atom no-outcomes)))))

;(let [new-inits? (not= (select-keys @init-sets-atom @precond-vars-atom)
;                             (select-keys (swap! init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))]
;        (when new-inits?
;          (extend-hla! precond-set-hla init-sets)
;          (reset! precond-vars-atom (clojure.set/union (precond-var-set precond-set-hla) (util/keyset (:precond-map action))))
;          (reset! effect-sets-atom  (sequence-effect-set-maps (effect-sets precond-set-hla)
;                                                              (util/map-vals (fn [x] #{x}) (:effect-map action))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interleaving HLA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Interleaving HLA takes a set of refinements and interleaves their access
;; to a set of specified common ancestors. 
 ; Idea: greedily refine / execute everything except PrecondSet actions incl. key vars.
 ; When all refinements start with such a PrecondSet, 
  ; Choose a first group, s.t. all other preconds are independent
   ; 

; Once we start the first PC in a PrecondSet, we cannot falsify other PCs. 
; When a PC set can fire, it must ... but not an individual PC?

; IF one PC set refers only to parent(A) but not A, and others refer to A,
 ; We must consider all ways of interleaving, with that shared-var-set. 
; This does not occur if all refer to A and parent(A) since we must always achieve A first,
 ; and then we are committed? 

; Note AND-OR structure, ignored so far.  Assuming all ORs pushed to search space.
; Thus, we end up with X-product of choice points, + interleavings.

; Also, what really matters is order *preconditions*, not sets, are achieved.

(declare make-interleaving-hla-refinement)

(deftype SAS-Interleaving-HLA [refinements shared-var-set] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union (map precond-var-set (apply concat refinements))))
    (effect-sets     [] (throw (UnsupportedOperationException.)))
    (pre-ref-pairs   [] (throw (UnsupportedOperationException.)))
    (compile-hla     [] (throw (UnsupportedOperationException.)))
    (extend-hla!     [init-sets par-effect-sets] (throw (UnsupportedOperationException.)))
  env/Action
    (action-name     [] [:!I refinements shared-var-set])
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s]
      (let [[stalled-refs rest-refs] (split-with #(= (type (first %)) ::SAS-Precond-Set-HLA) refinements)]
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
            (for [i (range (count refinements))
                  :let [[f & r] (nth refinements i)]]
              (make-interleaving-hla-refinement [f]               
               (concat (subvec refinements 0 i) [r] (subvec refinements (inc i)))
               shared-var-set)))))
    (cycle-level-           [s] nil))

(defn make-interleaving-hla [refinements shared-var-set]
  (println "MIH " (map #(map env/action-name %) refinements))
  (SAS-Interleaving-HLA (vec refinements) shared-var-set))

;; Greedily pull irrelevant actions out, until we get to a normalized HLA
(defn make-interleaving-hla-refinement [pre-actions refinements shared-var-set]  
;  (println (count refinements))
;  (println (map type pre-actions) (map type refinements) (map #(map type %) refinements))
  (println "MIHR" (map env/action-name pre-actions) (map #(map env/action-name %) refinements))
  (loop [in-refinements refinements, out-refinements [], pre-actions pre-actions]
    (if-let [[f & r] (seq in-refinements)]
      (let [[front back] (split-with #(or (empty? (clojure.set/intersection shared-var-set (precond-var-set %)))
                                          (env/primitive? %)) f)]
        (recur r (if (seq back) (conj out-refinements back) out-refinements) (concat pre-actions front)))
      (concat pre-actions (when (seq out-refinements) [(make-interleaving-hla out-refinements shared-var-set)])))))
  






;; Ideas here:
 ; If actions can be partitioned such that effects of each set disjoint with preconditions of all other sets,
   ; Such sets can be ordered arbitrarily.
     ; (+ caveat about idempotent effects)
 ; Within a given set, ones with same effects can be ordered arbitrarily.

 ; Finally, generate interleavings ...

;; Watch out: what happens when single action establishes multiple preconditions, e.g. .. 
;; TODO: need to treat subsets (i.e., transitive closure edges) specially.



;; Getting/extending HLA, extracting best-effort info for these init-sets, must be separate.
;; Parent will ahve to store some sort of ref to old prec/effect sets to detect change, since others may have extended since.

;; TODO: handle effect merges properly.
;; TODO: make sure we don't waste our time on new descendant values. (easy, just use current context.)
; Note: in this framework, ancestor in CG does not entail ordering? 
 ; Can we create graph for this bit too, so we reuse ?
; Adding to init, can totally change a-p graph.  

; Question; how do we handle A-P actions generally (establishing 1 may change init for other). 
; Question: can we just do all of this on the fly ? 

;; Want to look at acyclic paths, which include at most one free-action. (with no precond on var.)
;; Two things we can do here; recursive style (works from any src, more caching) or direct style
 ;; (avoid cycles, more focused description/pruning, but less caching and less general). 

;; TODO: induce stronger preconditions for refinements? 
;; TODO: split init-sets based on init val for var ?
;; Now: do forward search from inits.  For each init, keep track of outgoing HLAs, init sets.
  ;  Keep iterating until no new values added to inits.  
  ;  Also keep track of set of vals on all paths to val, to avoid cycles in exploration as possible.   
    ; If we keep all this info around in HLA, extending becomes easier.   



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top Level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: when can we use relaxed CG ?
(defn induce-raw-hierarchy [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        dtgs (sas-analysis/domain-transition-graphs vars actions)]
    (assert (graphs/dag? (sas-analysis/standard-causal-graph sas-problem)))
    (binding [*vars*          vars
              *var-val-sets*  (util/map-map (juxt :name (comp set :vals)) (vals vars))
              *var-levels*    (graphs/topological-sort-indices (sas-analysis/standard-causal-graph sas-problem))
              *extended-dtgs* dtgs
              *simple-dtgs*   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
              *hla-cache*     (HashMap.)]
;      (println "VVS"  *var-val-sets*)
      (let [goal-action (util/safe-singleton (get-in *extended-dtgs* [sas/goal-var-name sas/goal-false-val sas/goal-true-val]))
            goal-hla    (get-current-action-hla goal-action)]
        (extend-hla! goal-hla (util/map-vals (fn [x] #{x}) init) {})
        (hierarchy/SimpleHierarchicalEnv sas-problem [goal-hla])))))

(defn compile-hierarchy [h]
  (hierarchy/SimpleHierarchicalEnv (hierarchy/env h) (compile-refinement (hierarchy/initial-plan h))))

(defn induce-hierarchy [sas-problem]
  (compile-hierarchy (induce-raw-hierarchy sas-problem)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Printing  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmulti pretty-print-action (fn [h done-set] (type h)))

(defn pretty-print-hla [h #^HashSet done-set]
  (when-not (.contains done-set h)
    (.add done-set h)
    (println (str "\nRefs for HLA" (env/action-name h)) (precond-var-set h)  (effect-sets h))
    (doseq [ref (map second (pre-ref-pairs   h))]
      (println " " (util/str-join ", " (map env/action-name ref))))
    (doseq [ref (map second (pre-ref-pairs   h)), a ref]
      (pretty-print-action a done-set))))

(defmethod pretty-print-action :default [h ds] (pretty-print-hla h ds))
(defmethod pretty-print-action ::env/FactoredPrimitive [h ds] nil)


(defn pretty-print-hierarchy [hierarchy]
  (let [hs (HashSet.), ip (:initial-plan hierarchy)]
    (println "\nInitial plan is:" (map env/action-name ip ))
    (doseq [a ip] (pretty-print-action a hs))))










;(induce-hierarchy  (make-sas-problem-from-pddl (prln (write-infinite-taxi-strips2 (make-random-infinite-taxi-env 2 2 1)))))

(comment
  ; not needed anymore?
  
  
(defn find-all-acyclic-paths 
  ([var init-val-set goal-val reverse-dtg]
     (find-all-acyclic-paths var init-val-set goal-val reverse-dtg nil #{} true))
  ([var init-val-set goal-val reverse-dtg plan-suffix stack-val-set can-use-free?]
;     (println "FACP" var init-val-set goal-val)
     (when (and (seq init-val-set) (not (contains? stack-val-set goal-val)))
       (if (contains? init-val-set goal-val)
           (cons plan-suffix 
                 (find-all-acyclic-paths var (disj init-val-set goal-val) goal-val reverse-dtg plan-suffix 
                                         stack-val-set can-use-free?))
         (apply concat
           (for [[pval actions] (get reverse-dtg goal-val)
                 a              actions
                 :let  [action-free? (not (contains? (:precond-map a) var))]
                 :when (or (not action-free?) can-use-free?)]
             (find-all-acyclic-paths var init-val-set pval reverse-dtg (cons a plan-suffix) 
                                     (conj stack-val-set goal-val) (and can-use-free? (not action-free?)))))))))
  

(defn induce-vv-hla- [var goal-val init-sets]
  (util/print-debug 2 "Inducing HLA to get" var "to val" goal-val "from" (init-sets var))
  (let [inits        (init-sets var)
        reverse-dtg  (*reverse-dtgs* var)
        paths        (find-all-acyclic-paths var inits goal-val reverse-dtg)
        refs-results (filter identity (map #(progress-refinement % init-sets ) paths))]
    (if (and (util/singleton? refs-results) (util/singleton? (ffirst refs-results)))
        (first (ffirst refs-results))
      (when (seq refs-results)
        (assert (apply = (map util/keyset (map second refs-results)))) ;; Otherwise, no-effect not handled properly when not in PC.
        (SAS-VV-HLA var goal-val 
                    (set (for [[ref _] refs-results, a ref, v (precond-var-set a)] v))
                    init-sets 
                    (apply merge-with clojure.set/union (map second refs-results))
                    (map first refs-results))))))

)