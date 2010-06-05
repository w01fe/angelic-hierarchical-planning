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





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy* (fn [state first-action] :unknown))

(defn make-node-descendant [root goal-node remaining-actions] 
  (assert (is/optimal-solution goal-node))
  (if-let [[f & r] (seq remaining-actions)]
    ((*node-type-policy* root [goal-node f]) root goal-node remaining-actions)
    goal-node))


(defn sp-node-name [state actions]
  [state (map env/action-name actions)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Straight search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn next-transparent-node [root goal-node [f & r :as remaining-actions]]
  (let [state (is/goal-state goal-node)]
;    (println "T " (sp-node-name state remaining-actions) (is/max-reward goal-node)) (Thread/sleep 100)    
    (is/make-expanding-search (sp-node-name state remaining-actions) nil (is/max-reward goal-node)
      (lazy-seq
       (if (env/primitive? f)
         (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
           [(make-node-descendant root (is/make-goal-search ss (+ (is/max-reward goal-node) sr) 
                                                       (conj (is/optimal-solution goal-node)  f)) r)])
         (for [ref (hierarchy/immediate-refinements f state)]
           (make-node-descendant root goal-node (concat ref r))))))))

(defn make-incremental-dijkstra-sa-search 
  ([state action] (make-incremental-dijkstra-sa-search (sa-node-name state action) state action))
  ([name state action]
     (let [node (is/make-goal-search state 0 [])]
       (is/make-incremental-dijkstra-search name [(next-transparent-node [node action] node [action])] nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; State Abstraction ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def #^HashMap *problem-cache* nil)

(defn contextualize-goal [parent-goal child-goal]
    (assert (is/optimal-solution child-goal))
    (is/make-goal-search 
     (env/apply-effects (is/goal-state parent-goal)       (env/extract-effects (is/goal-state child-goal)))
     (+                 (is/max-reward parent-goal)       (is/max-reward child-goal))
     (concat            (is/optimal-solution parent-goal) (is/optimal-solution child-goal))))

(defn next-recursive-node [root goal-node [f & r :as remaining-actions] ]
  (let [state   (is/goal-state goal-node)
        context (env/precondition-context f state)
        in-name (sa-node-name state f context)]
;    (println "R " (sp-node-name state remaining-actions) (is/max-reward goal-node)) (Thread/sleep 100)
    (is/make-transformed-search 
     (sp-node-name state remaining-actions)
     (is/get-cached-search *problem-cache* in-name
       (make-incremental-dijkstra-sa-search in-name (env/get-logger state context) f))
     #(make-node-descendant root (contextualize-goal goal-node %) r)
     (is/max-reward goal-node)
     nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

















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

(defn if-cycle-fn [if-cycle else]
  (fn [[parent-node parent-action] [node action]]
;    (println (env/action-name action) (env/action-name parent-action) (hierarchy/cycle-level action (is/goal-state node)) (hierarchy/cycle-level parent-action (is/goal-state parent-node)) )
    (if (util/aand (hierarchy/cycle-level action (is/goal-state node))
                   (= it (hierarchy/cycle-level parent-action (is/goal-state parent-node))))
        if-cycle else)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Drivers   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn sahucs-flat [henv]
  (hierarchical-search henv (constantly next-transparent-node)
    make-incremental-dijkstra-sa-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv (constantly next-recursive-node)
    make-incremental-dijkstra-sa-search))

(defn sahucs-dijkstra [henv]
  (hierarchical-search henv (if-cycle-fn next-transparent-node next-recursive-node) 
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