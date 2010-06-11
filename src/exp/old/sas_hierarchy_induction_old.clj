(ns exp.sas-hierarchy-induction
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util  [graphs :as graphs]]
            [exp [env :as env]  [hierarchy :as hierarchy] [sas :as sas] [sas-analysis :as sas-analysis]])
  (:import [java.util HashMap]))


;; Right now, this is only for DAGs. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def no-effect ::NO-EFFECT)
(defn disjoin-effect-maps [m1 m2])


(def *vars* nil)
(def *reverse-dtgs* nil)
(def #^HashMap *hla-cache* nil) ; a map from [action-name] to map from init-sets to action.

(def *ap-key* :!A)
(def *vv-key* :!VV)

(defprotocol SAS-Induced-Action
  (precond-var-set [a])
  (initial-sets    [a])
  (effect-sets     [a]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a)))
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))})

(defn vv-hla-name [var val] [*vv-key* var val])
(deftype SAS-VV-HLA     [var val precond-vars init-sets effect-sets refinements]
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (initial-sets    [] init-sets)
    (effect-sets     [] effect-sets)
  env/Action
    (action-name [] (vv-hla-name var val))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] #_ (util/assert-is (util/subset? (util/keyset effect-sets) precond-vars)) precond-vars)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] refinements)
    (cycle-level-           [s] nil))

(defn action-hla-name [action] [*ap-key* (env/action-name action)])
(deftype SAS-Action-HLA [action  precond-vars init-sets effect-sets refinements]
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (initial-sets    [] init-sets)
    (effect-sets     [] effect-sets)
  env/Action
    (action-name [] (action-hla-name action))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] #_ (util/assert-is (util/subset? (util/keyset effect-sets) precond-vars)) precond-vars)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] refinements)
    (cycle-level-           [s] nil))


(declare induce-action-hla induce-vv-hla)

;; TODO: handle effect merges properly.
;; TODO: make sure we don't waste our time on new descendant values. (easy, just use current context.)
; Note: in this framework, ancestor in CG does not entail ordering? 
 ; Can we create graph for this bit too, so we reuse ?
; Adding to init, can totally change a-p graph.  

; Question; how do we handle A-P actions generally (establishing 1 may change init for other). 
; Question: can we just do all of this on the fly ? 

(defn progress-refinement [prim-ref init-sets ]
  (util/print-debug 2 "Progressing plan" prim-ref)
  (loop [prim-ref prim-ref, hla-ref [], plan-effect-sets {}]
    (if (empty? prim-ref)
        [hla-ref plan-effect-sets]
      (let [a     (first prim-ref)
            hla-a (induce-action-hla a (merge init-sets plan-effect-sets) )]
        (recur (rest prim-ref) (conj hla-ref hla-a) (merge plan-effect-sets (effect-sets hla-a)))))))

;; Want to look at acyclic paths, which include at most one free-action. (with no precond on var.)
;; Two things we can do here; recursive style (works from any src, more caching) or direct style
 ;; (avoid cycles, more focused description/pruning, but less caching and less general). 

;; TODO: induce stronger preconditions for refinements? 
;; TODO: split init-sets based on init val for var ?
;; Now: do forward search from inits.  For each init, keep track of outgoing HLAs, init sets.
  ;  Keep iterating until no new values added to inits.  
  ;  Also keep track of set of vals on all paths to val, to avoid cycles in exploration as possible.   
    ; If we keep all this info around in HLA, extending becomes easier.   
(defn induce-vv-hla- [var goal-val init-sets]
  (util/print-debug 2 "Inducing HLA to get" var "to val" goal-val "from" (init-sets var))
  (let [inits        (init-sets var)
        reverse-dtg  (*reverse-dtgs* var)
        forward-edges (for [[fval pmap] reverse-dtg, [pval _] pmap] [pval fval])
        bad-edges    (set (graphs/find-cyclic-edges forward-edges (seq inits) [goal-val]))
        reverse-dtg  (util/map-map (fn [[fval pmap]]
                                     [fval (util/filter-map (fn [[pval _]] (not (contains? bad-edges [pval fval]))) pmap)]) reverse-dtg)
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

;; Ideas here:
 ; If actions can be partitioned such that effects of each set disjoint with preconditions of all other sets,
   ; Such sets can be ordered arbitrarily.
     ; (+ caveat about idempotent effects)
 ; Within a given set, ones with same effects can be ordered arbitrarily.

 ; Finally, generate interleavings ...

;; Watch out: what happens when single action establishes multiple preconditions, e.g. .. 
;; TODO: need to treat subsets (i.e., transitive closure edges) specially.

(defn induce-action-hla- [a init-sets ]
  (util/print-debug 2 "Inducing HLA for preconds + action" (:name a))
  (let [first-bits (doall (for [[pvar pval] (:precond-map a)
                                :when (not (= (init-sets pvar) #{pval}))]
                            (induce-vv-hla pvar pval init-sets )))]
;    (println (:name a) (count first-bits))
;    (doseq [b first-bits] (println "\n" (env/action-name b) "\n\n"))
    (when (every? identity first-bits)
     (if (empty? first-bits)
         a
       (let [bit (util/safe-singleton first-bits)]
         (assert (= ((effect-sets bit) (:var bit)) #{(:val bit)}))
         (SAS-Action-HLA 
          a 
          (clojure.set/union (util/keyset (:precond-map a)) (precond-var-set bit))
          init-sets
          (merge (effect-sets bit) (util/map-vals (fn [x] #{x}) (:effect-map a)))
          [[bit a]]))))))


;; TODO: figure out how much to generalize here.
(defn cached-induce [name init-sets result-fn]
  (let [entries (.get *hla-cache* name)]
    (assert (not (identical? entries :STACK)))
    (if-let [v (first (filter #(let [ks (precond-var-set %)] 
                                 (= (select-keys init-sets ks) (select-keys (initial-sets %) ks))) 
                              entries))]
        (do (util/print-debug 3 "Cache hit for" name) 
            v)
      (do (.put *hla-cache* name :STACK)
          (let [ret (result-fn)]
            (assert ret) ;; If we run into this, need to figure out how to properly cache failures.
            (.put *hla-cache* name (cons ret entries))
            ret)))))

(defn induce-action-hla [a init-sets]
  (cached-induce (action-hla-name a) init-sets #(induce-action-hla- a init-sets)))

(defn induce-vv-hla [var goal-val init-sets ]
  (cached-induce (vv-hla-name var goal-val) init-sets #(induce-vv-hla- var goal-val init-sets)))

(defn induce-hierarchy [sas-problem]
  (let [{:keys [vars actions init]} sas-problem]
    (binding [*vars*         vars
              *reverse-dtgs* (sas-analysis/reverse-domain-transition-graphs vars actions)
              *hla-cache*    (HashMap.)              
              ]
      (hierarchy/SimpleHierarchicalEnv sas-problem 
        [(util/make-safe 
          (induce-action-hla (util/safe-singleton (get-in *reverse-dtgs* [sas/goal-var-name sas/goal-true-val sas/goal-false-val]))
                             (util/map-vals (fn [x] #{x}) init)))]))))





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