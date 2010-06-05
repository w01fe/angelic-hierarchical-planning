(ns exp.ahois
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy]
            [exp.incremental-search :as is])
  (:import  [java.util HashMap]))


; Angelic hierarchy of optimal incremental searches

;; Cleaned up version of sahdd, should hopefully be more efficient, include SAHA as well,
;; also ALTs, goal abstractions, more info propagation.


;; Note: true state abstraction condition: every optimal solution of A is optimal solution of B. 
; Note:  We should still (unfortunately) never close open subproblems with cycles.  

 
;; NOTE: must handle reward decreasses of parital nodes properly. (first versions still mess this up).


;; TODO: fancier info going up
;; TODO: fancier goals, etc.
;; TODO: tests
;; TODO: metalevel policies
;; TODO: merge searches and nodes
;; TODO: more general ways to express sequencing, primitives?
;; TODO: think about suffix sharing and node merging, as much as possible. (ALT-like?)
;; TODO: ALTs option for dijkstra?

; TODO TODO: watch for equality. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sa-node-name 
  ([state action] (sa-node-name state action (env/precondition-context action state)))
  ([state action context] [(env/extract-context state context) (env/action-name action)]))

(defn make-eager-primitive-search-or-nil [state action]
  (when (env/applicable? action state)
    (let [name    (sa-node-name state action)
          [ss sr] (env/successor action state)]
      (reify is/IncrementalSearch
        (node-name        [] name)
        (goal-state       [] ss)
        (max-reward       [] sr)
        (optimal-solution [] [action])
        (next-results     [min-reward] (throw (UnsupportedOperationException.)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Straight search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-search-node)

(defn make-incremental-dijkstra-sa-search 
  ([state action] (make-incremental-dijkstra-sa-search (sa-node-name state action) state action))
  ([name state action]
     (is/make-incremental-dijkstra-search name 
       [(make-search-node :transparent state 0 [] [action])] nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; State Abstraction ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment 
  (def #^HashMap *problem-cache* nil)

  (defn contextualize-goal [state reward sol goal]
    (assert (is/optimal-solution goal))
    (make-goal-search 
     (env/apply-effects state (env/extract-effects (is/goal-state goal)))
     (+ reward (is/max-reward goal))
     (concat sol (is/optimal-solution goal))))



  (defn make-abstracted-sp-search [context-state context-reward remaining-actions goal-search]
    (let [context (env/precondition-context action state)
          in-name (sa-node-name state action context)]
      (is/make-transformed-search [state (env/action-name action)]
                                  (get-cached-search *problem-cache* in-name
                                                     (make-incremental-dijkstra-sa-search (env/get-logger state context) action))
                                  #(make-node-descendant (contextualize-goal-search state reward sol)) ( (partial contextualize-goal-search context-state context-reward ))))
  
    )

  (defn generalize-outcome-pair [[outcome-state reward] gen-state reward-to-gen-state]
    [(vary-meta (env/apply-effects gen-state (env/extract-effects outcome-state)) assoc 
                :opt (concat (:opt (meta gen-state)) (:opt (meta outcome-state))))
     (+ reward reward-to-gen-state)])

  (defn lift-partial-result [partial-result context-state context-reward]
    (let [{:keys [result-pairs max-reward]} partial-result]
      (PartialResult (map #(generalize-outcome-pair % context-state context-reward) result-pairs)
                     (+ max-reward context-reward))))

  (defn make-abstracted-search [is context-state context-reward]
    (is/make-transformed-search is [context-state (second (node-name is))] 
                                result-fn context-reward))

;; ???
  (defn make-search-in-context [is context-state context-reward remaining-actions]
    (is/make-transformed-search is [context-state (second (node-name is))] 
                                result-fn context-reward))

;; TODO: do away with sa-node-name, or something.

  (defn make-abstracted-incremental-dijkstra-sa-search [state reward sol action remaining-actions]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-search-node)
(def *node-type-policy* (fn [state first-action] :unknown))

(defn sp-node-name [state actions]
  [state (map env/action-name actions)])

(defn make-node-descendant 
  ([goal-node remaining-actions] 
     (make-search-node (when-first [f remaining-actions] (*node-type-policy* (is/goal-state goal-node) f)) goal-node remaining-actions))
  ([state reward sol remaining-actions]
      (make-search-node (when-first [f remaining-actions] (*node-type-policy* state f))
                        state reward sol remaining-actions)))

(defn make-search-node 
  ([type goal-node remaining-actions]
     (assert ( is/optimal-solution goal-node))
     (make-search-node type (is/goal-state goal-node) (is/max-reward goal-node) (is/optimal-solution goal-node)))
  ([type state reward sol remaining-actions]
     (if-let [[f & r] (seq remaining-actions)]
       (case type 
             :transparent
             (is/make-expanding-search (sp-node-name state remaining-actions) nil reward
                                       (lazy-seq
                                        (if (env/primitive? f)
                                          (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
                                            [(make-node-descendant ss (+ reward sr) (conj sol f) r)])
                                          (for [ref (hierarchy/immediate-refinements f state)]
                                            (make-node-descendant state reward  sol (concat ref r))))))
             :recursive
             (make-incremental-dijkstra-sa-search state f))
       (is/make-goal-search state reward sol))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)

(defn hierarchical-search [henv policy search-maker]
  (binding [*node-type-policy* policy
            *problem-cache*    (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (search-maker init tla)]
      (when-let [sol (first (is/next-results top Double/NEGATIVE_INFINITY))]
        (assert (is/optimal-solution sol))
        [(map identity #_env/action-name (is/optimal-solution sol)) (is/max-reward sol) ]))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Drivers   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn sahucs-flat [henv]
  (hierarchical-search henv (constantly :transparent)
    make-incremental-dijkstra-sa-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv (constantly :recursive)
    make-incremental-dijkstra-sa-search))




(comment
 (let [e (make-random-taxi-env 3 3 3 2) h (simple-taxi-hierarchy e)]  
  (println "ucs" (run-counted #(second (uniform-cost-search e))))
  (doseq [alg `[sahtn-dijkstra sahucs-flat sahucs-simple sahucs-dijkstra sahucs-inverted]]
         (time (println alg (run-counted #(second ((resolve alg) h)))))))
 
 (let [e (exp.nav-switch/make-random-nav-switch-env 2 0) h (exp.nav-switch/make-nav-switch-hierarchy e false)]  
;  (println "ucs" (run-counted #(second (uniform-cost-search e))))
  (doseq [alg `[sahucs-flat exp.ahois/sahucs-flat]]
         (time (println alg (run-counted #(second (debug 2 ((resolve alg) h))))))))
 )


;; TODO: compare performance to other algorithms.  


;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 