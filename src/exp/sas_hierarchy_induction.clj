(ns exp.sas-hierarchy-induction
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  (:import [java.util HashMap]))


;; Right now, this is only for DAGs. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def no-effect-val ::NO-EFFECT)
(def no-effect-set #{no-effect-val})

(defn disjoin-effect-set-maps [m1 m2]
  (util/map-map 
   (fn [k] (clojure.set/union (get m1 k no-effect-set) (get m2 k no-effect-set)))
   (distinct (concat (keys m1) (keys m2)))))

(defn sequence-effect-set-maps [m1 m2]
  (merge m1 m2))

(defn apply-effect-set-map [init-sets effect-set-map]
  (reduce (fn [m [ek evs]]
            (let [ovs (util/safe-get init-sets ek)]
              (assoc m ek (if (contains? evs no-effect-val) (clojure.set/union ovs (disj evs no-effect-val)) evs))))
          init-sets effect-set-map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Global bindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *vars* nil)
(def *extended-dtgs* nil) ; Map from var to map from prev val to map from post val to list of actions.
(def *simple-dtgs* nil)   ; Map from var to edge list.
(def *var-val-sets* nil)  ; Map from var name to set of all vals.
(def #^HashMap *hla-cache* nil) ; a map from [action-name] to map from init-sets to action.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






;; Difference from precond-var-set and precondition-context is for primitives (?)
(defprotocol SAS-Induced-Action
  (precond-var-set [a])
;  (initial-sets    [a])
  (effect-sets     [a]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
;     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a))) ;?
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; VV HLAs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare get-current-action-hla extend-action-hla!)

;; TODO: special treatment for "free"  vars without self-loops.

(defn vv-hla-name [var src-val dst-val] [:!VV src-val dst-val])

; successor-map is a map from dst-val to list of [ap-hla next-vv-hla] pairs. 
(deftype SAS-VV-HLA  [var src-val dst-val src?-atom init-sets-atom precond-vars-atom effect-sets-atom successor-map-atom]
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
  env/Action
    (action-name [] (vv-hla-name var src-val dst-val))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] @precond-vars-atom)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] (apply concat (vals @successor-map-atom)))
    (cycle-level-           [s] nil))

(defn get-current-vv-hla [var src-val dst-val]
  (util/cache-with *hla-cache* (vv-hla-name var src-val dst-val)
    (if (= src-val dst-val)
      (SAS-VV-HLA var src-val dst-val (atom true) (atom *var-val-sets*) (atom #{var}) (atom {}) (atom {}))      
      (SAS-VV-HLA var src-val dst-val (atom false) (atom {})            (atom #{var}) (atom {}) (atom {})))))

(declare extend-vv-hla-edge!)

(defn designate-vv-hla-src! [hla]
  (let [{:keys [var src-val dst-val src?-atom]} hla]
    (reset! src?-atom true)
    (doseq [[s t] (graphs/find-acyclic-edges (*simple-dtgs* var) [src-val] [dst-val])]
      (let [sn (get-current-vv-hla var s dst-val)]
        (when-not (contains? @(:successor-map-atom sn) t)
          (when (seq @(:init-sets-atom sn)) (println "Warning: adding outgoing edges! (sas_hierarchy_induction)"))
          (swap! @(:successor-map-atom sn) assoc t
            (doall (for [a (util/safe-get-in *extended-dtgs* var s t)] 
                     [(get-current-action-hla a var) (get-current-vv-hla var t dst-val)])))
          (doseq [e (util/safe-get @(:successor-map-atom sn) t)]
            (extend-vv-hla-edge! sn e @(:init-sets sn))))))))


(defn extend-vv-hla! 
  "Extend this HLA to cover new init-sets, as needed. src? indicates whether this value can be a source from a descendent."
  [hla init-sets src?]
  (let [{:keys [var src-val dst-val src?-atom init-sets-atom precond-vars-atom effect-sets-atom successor-map-atom]} hla
        new-src?   (and src? (not @src?-atom))
        new-inits? (not= (select-keys @init-sets-atom @precond-vars-atom)
                         (select-keys (swap! @init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))]
    (assert (= (get init-sets var) #{src-val}))
    (when new-src? 
      (designate-vv-hla-src! hla))
    (when new-inits?
      (doseq [e (vals @successor-map-atom)] (extend-vv-hla-edge! hla e @init-sets-atom)))
    (when (or new-src? new-inits?)
      (let [successors (map second (apply concat (vals @successor-map-atom)))]
        (reset! precond-vars-atom (apply clojure.set/union       (map precond-var-set successors)))
        (reset! effect-sets-atom  (apply disjoin-effect-set-maps (map effect-sets     successors)))))))

(defn extend-vv-hla-edge! 
  "Extend this VV-HLA edge to cover new init-sets, as needed."
  [hla [a next-vv-hla] init-sets]
  (extend-action-hla! a init-sets)
  (extend-vv-hla! next-vv-hla (effect-sets a) false))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Precondition Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each precond HLA is not cached, and is owned by a particular action.
;; It just aggregates sets of src vv-hla nodes, more or less.
;; src-map-atom maps from src vals to sas-vv-hla instances.  Init-sets describes current init-sets.

(deftype SAS-Precond-HLA [var dst-val src-map-atom] :as this
  SAS-Induced-Action
    (precond-var-set [] (apply clojure.set/union       (map precond-var-set (vals src-map-atom))))
    (effect-sets     [] (apply disjoin-effect-set-maps (map effect-sets     (vals src-map-atom))))
  env/Action
    (action-name [] (throw (UnsupportedOperationException.)))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [(util/safe-get @src-map-atom (env/get-var s var))])
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

;; Each precond HLA is not cached, and is owned by a particular action.
;; It just aggregates sets of src vv-hla nodes, more or less.
;; src-map-atom maps from src vals to sas-vv-hla instances.  Init-sets describes current init-sets.

(deftype SAS-Precond-Set-HLA [hard-preconds soft-precond?] :as this
  SAS-Induced-Action
    (precond-var-set [] (if soft-precond? (precond-var-set soft-precond?) #{}))
    (effect-sets     [] (if soft-precond? (effect-sets     soft-precond?)  {}))
  env/Action
    (action-name [] (throw (UnsupportedOperationException.)))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (precond-var-set this))
  hierarchy/HighLevelAction
    (immediate-refinements- [s] (assert (env/state-matches-map? s hard-preconds)) (if soft-precond? [soft-precond?] []))
    (cycle-level-           [s] nil))

(defn make-precond-set-hla [hard-preconds soft-precond?] 
  (SAS-Precond-Set-HLA hard-preconds soft-precond?))

(defn extend-precond-set-hla! [hla init-sets]
  (assert (every? (fn [[k v]] (contains? (get init-sets k) v)) (:hard-preconds hla)))
  (when-let [p (:soft-precond? hla)] (extend-precond-hla! p init-sets)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An action.  
;; TODO: think about splitting this based on which var it's being used for.
;; TODO: make fancier.
;; TODO: how do we go in parallel? Need to simulate parallel execution, look at pairs of choice points, ETC ? 
;; For now, assume at most one unsatisfied precond.

(defn action-hla-name [action] [:!A (env/action-name action)])

(deftype SAS-Action-HLA [action precond-set-hla init-sets-atom precond-vars-atom effect-sets-atom]
  SAS-Induced-Action
    (precond-var-set [] @precond-vars-atom)
    (effect-sets     [] @effect-sets-atom)
  env/Action
    (action-name     [] (action-hla-name action))
    (primitive?      [] false)
  env/ContextualAction 
    (precondition-context [s] @precond-vars-atom)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] [precond-set-hla action])
    (cycle-level-           [s] nil))


(defn get-current-action-hla [action var]
  (let [preconds     (:precond-map action)
        rem-preconds (dissoc preconds var)]
    (assert (<= (count rem-preconds) 1))
    (util/cache-with *hla-cache* (action-hla-name action)
      (SAS-Action-HLA action
        (make-precond-set-hla (select-keys preconds [var]) (make-precond-hla (key (first rem-preconds)) (val (first rem-preconds))))
        (atom {}) (atom (util/keyset preconds)) (atom {})))))

(defn extend-action-hla! [hla init-sets]
  (let [{:keys [action precond-set-hla init-sets-atom precond-vars-atom effect-sets-atom]} hla
        new-inits? (not= (select-keys @init-sets-atom @precond-vars-atom)
                         (select-keys (swap! @init-sets-atom #(merge-with clojure.set/union % init-sets)) @precond-vars-atom))]
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


(def *vars* nil)
(def *extended-dtgs* nil) ; Map from var to map from prev val to map from post val to list of actions.
(def *simple-dtgs* nil)   ; Map from var to edge list.
(def *var-val-sets* nil)  ; Map from var name to set of all vals.
(def #^HashMap *hla-cache* nil) ; a map from [action-name] to map from init-sets to action.

(defn induce-hierarchy [sas-problem]
  (let [{:keys [vars actions init]} sas-problem]
    (binding [*vars*          vars
              *extended-dtgs* (sas-analysis/domain-transition-graphs vars actions)
              *simple-dtgs*   (util/map-vals (fn [dtg] (for [[pval emap] dtg, [eval _] emap] [pval eval])) *extended-dtgs*)
              *var-val-sets*  (util/map-map (juxt :name :vals) vars)
              *hla-cache*     (HashMap.)]
      (let [goal-action (util/safe-singleton (get-in *extended-dtgs* [sas/goal-var-name sas/goal-false-val sas/goal-true-val]))
            goal-hla    (get-current-action-hla goal-action sas/goal-var-name)]
        (extend-action-hla! goal-hla (util/map-vals (fn [x] #{x}) init))
        (hierarchy/SimpleHierarchicalEnv sas-problem [goal-hla])))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Printing  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmulti pretty-print-action type)

(defn pretty-print-hla [h]
  (println (str "\nRefs for HLA" (env/action-name h)) (precond-var-set h) #_ (effect-sets h))
  (doseq [ref (:refinements h)]
    (println " " (util/str-join ", " (map env/action-name ref))))
  (doseq [ref (:refinements h), a ref]
    (pretty-print-action a)))

(defmethod pretty-print-action ::SAS-VV-HLA [h] (pretty-print-hla h))
(defmethod pretty-print-action ::SAS-Action-HLA [h] (pretty-print-hla h))
(defmethod pretty-print-action ::env/FactoredPrimitive [h] nil)


(defn pretty-print-hierarchy [hierarchy]
  (pretty-print-action (first (:initial-plan hierarchy))))










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