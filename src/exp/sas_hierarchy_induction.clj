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
(defprotocol SAS-Induced-Action
  (precond-var-set [a])
;  (initial-sets    [a])
  (effect-sets     [a])
  (pre-ref-pairs   [a])
  (compile-hla     [a]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
;     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a))) ;?
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))
     :pre-ref-pairs   (fn [a] (throw (UnsupportedOperationException.)))
     :compile-hla     (fn [a] a)})

(deftype SAS-Compiled-HLA [name precond-vars effects refinements-and-preconditions ref-generator] :as this
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (effect-sets     [] effects)
    (pre-ref-pairs   [] refinements-and-preconditions)
    (compile-hla     [] this)
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

;; TODO: special treatment for "free"  vars without self-loops.

(defn vv-hla-name [var src-val dst-val] [:!VV src-val dst-val])

; successor-map is a map from dst-val to list of [ap-hla next-vv-hla] pairs. 
(deftype SAS-VV-HLA  [var src-val dst-val src?-atom dirty?-atom init-sets-atom precond-vars-atom effect-sets-atom successor-map-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
    (pre-ref-pairs   [] (if (= src-val dst-val) [[{} []]] 
                            (for [vs (vals @successor-map-atom), v vs] [{} v])))
    (compile-hla     [] (if (= src-val dst-val) [] (default-compile-hla #_-noflatten this)))
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
      (SAS-VV-HLA var src-val dst-val (atom true) (atom false) (atom *var-val-sets*) (atom #{var}) (atom {}) (atom {}))      
      (SAS-VV-HLA var src-val dst-val (atom false) (atom false) (atom {})            (atom #{var}) (atom no-outcomes) (atom {})))))

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
    (util/assert-is (or (seq edges) (= src-val dst-val)))
    (reset! src?-atom true)
    (when any-new? 
      (doseq [s (distinct (map first edges))]
        (reset! (:dirty?-atom (get-current-vv-hla var s dst-val)) true)))))


(defn extend-vv-hla! 
  "Extend this HLA to cover new init-sets, as needed. src? indicates whether this value can be a source from a descendent."
  [hla init-sets src?]
  (let [{:keys [var src-val dst-val src?-atom dirty?-atom init-sets-atom precond-vars-atom successor-map-atom]} hla]
;    (println "Extend" (:var hla) (:src-val hla) (:dst-val hla) new-inits? (count @successor-map-atom))
    (util/assert-is (= (util/safe-get init-sets var) #{src-val}))
    (when (and src? (not @src?-atom)) (designate-vv-hla-src! hla))
    (when (or (not= (select-keys @init-sets-atom @precond-vars-atom)
                    (select-keys (swap! init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))
              @dirty?-atom) 
      (reset! dirty?-atom false)
      (doseq [es (vals @successor-map-atom), e es] (extend-vv-hla-edge! hla e @init-sets-atom)))))

;; TODO: make sure this is general enough handling of precond sets.
(defn extend-vv-hla-edge! 
  "Extend this VV-HLA edge to cover new init-sets, as needed."
  [hla [a next-vv-hla] init-sets]
  (assert (not (= (:src-val hla) (:dst-val hla))))
  (extend-action-hla! a init-sets)
;  (println (env/action-name hla) init-sets (effect-sets hla) (effect-sets a) (effect-sets next-vv-hla))
  (extend-vv-hla! next-vv-hla (apply-effect-set-map init-sets (effect-sets a)) false)

  (swap! (:precond-vars-atom hla) clojure.set/union       (precond-var-set a) (precond-var-set next-vv-hla))
  (swap! (:effect-sets-atom hla)  disjoin-effect-set-maps (sequence-effect-set-maps (effect-sets a) (effect-sets next-vv-hla)))
  (util/assert-is (= (get @(:effect-sets-atom hla) (:var hla)) #{(:dst-val hla)}) "%s" [(env/action-name hla)]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precondition Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each precond HLA is not cached, and is owned by a particular action.
;; It just aggregates sets of src vv-hla nodes, more or less.
;; src-map-atom maps from src vals to sas-vv-hla instances.  Init-sets describes current init-sets.

(deftype SAS-Precond-HLA [var dst-val src-map-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union       (map precond-var-set (vals @src-map-atom))))
    (effect-sets     [] (apply disjoin-effect-set-maps (map effect-sets     (vals @src-map-atom))))
    (pre-ref-pairs   [] (if (util/singleton? @src-map-atom) 
                            [[{} [(first (vals @src-map-atom))]]]
                          (for [[k v] @src-map-atom] [{var k} [v]])))
    (compile-hla     [] (default-compile-hla this))
  env/Action
    (action-name [] [:precond var dst-val (System/identityHashCode this)])
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [[(util/safe-get @src-map-atom (env/get-var s var))]])
    (cycle-level-           [s] nil))

(defn make-precond-hla [var dst-val] 
  (SAS-Precond-HLA var dst-val (atom {})))

(defn extend-precond-hla! [hla init-sets]
  (let [{:keys [var dst-val src-map-atom]} hla]
    (doseq [src-val (util/safe-get init-sets var)]
      (when-not (contains? @src-map-atom src-val)
        (swap! src-map-atom assoc src-val (get-current-vv-hla var src-val dst-val)))
      (extend-vv-hla! (util/safe-get @src-map-atom src-val) (assoc init-sets var #{src-val}) true))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precondition Set Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Preconds are ordered, max-level (deepest) first.
(deftype SAS-Precond-Set-HLA [ordered-preconds] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union        (map precond-var-set ordered-preconds)))
    (effect-sets     [] (apply sequence-effect-set-maps (map effect-sets ordered-preconds)))
    (pre-ref-pairs   [] [[{} ordered-preconds]])
    (compile-hla     [] (default-compile-hla this))
  env/Action
    (action-name [] [:ps (System/identityHashCode this)])
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [ordered-preconds])
    (cycle-level-           [s] nil))

(defn make-precond-set-hla [precond-map] 
  (SAS-Precond-Set-HLA (map (partial apply make-precond-hla) (sort-by (comp - *var-levels* key) precond-map))))

(defn extend-precond-set-hla! [hla init-sets]
  (let [{:keys [ordered-preconds]} hla]
;    (println (map :var ordered-preconds))
    (loop [init-sets init-sets, ordered-preconds ordered-preconds, used-vars #{}]
      (when-let [[f & r] (seq ordered-preconds)]        
        (extend-precond-hla! f init-sets)
        (assert (or (contains? used-vars (:var f))
                    (empty? (clojure.set/intersection used-vars (precond-var-set f)))))
        (recur (apply-effect-set-map init-sets (effect-sets f)) 
               r
               (clojure.set/union used-vars (precond-var-set f) (util/keyset (effect-sets f))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An action.  
;; TODO: think about splitting this based on which var it's being used for.
;; TODO: make fancier.
;; TODO: how do we go in parallel? Need to simulate parallel execution, look at pairs of choice points, ETC ? 
;; For now, assume at most one unsatisfied precond.

(defn action-hla-name [action] [:!A (env/action-name action)])

(deftype SAS-Action-HLA [action precond-set-hla init-sets-atom precond-vars-atom effect-sets-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
    (pre-ref-pairs   [] [[{} [precond-set-hla action]]])
    (compile-hla     [] (default-compile-hla this))    
  env/Action
    (action-name     [] (action-hla-name action))
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] @precond-vars-atom)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [[precond-set-hla action]])
    (cycle-level-           [s] nil))


(defn get-current-action-hla [action]
  (let [preconds     (:precond-map action)]
    (util/cache-with *hla-cache* (action-hla-name action)
      (SAS-Action-HLA action (make-precond-set-hla preconds) (atom {}) (atom (util/keyset preconds)) (atom no-outcomes)))))

(defn extend-action-hla! [hla init-sets]
  (assert (= (type hla) ::SAS-Action-HLA))
  (let [{:keys [action precond-set-hla init-sets-atom precond-vars-atom effect-sets-atom]} hla
        new-inits? (not= (select-keys @init-sets-atom @precond-vars-atom)
                         (select-keys (swap! init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))]
    (when new-inits?
      (extend-precond-set-hla! precond-set-hla init-sets)
      (reset! precond-vars-atom (clojure.set/union (precond-var-set precond-set-hla) (util/keyset (:precond-map action))))
      (reset! effect-sets-atom  (sequence-effect-set-maps (effect-sets precond-set-hla)
                                                          (util/map-vals (fn [x] #{x}) (:effect-map action)))))))






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
              *var-val-sets*  (util/map-map (juxt :name :vals) vars)
              *var-levels*    (graphs/topological-sort-indices (sas-analysis/standard-causal-graph sas-problem))
              *extended-dtgs* dtgs
              *simple-dtgs*   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) dtgs)
              *hla-cache*     (HashMap.)]
      
      (let [goal-action (util/safe-singleton (get-in *extended-dtgs* [sas/goal-var-name sas/goal-false-val sas/goal-true-val]))
            goal-hla    (get-current-action-hla goal-action)]
        (extend-action-hla! goal-hla (util/map-vals (fn [x] #{x}) init))
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