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

(defn sa-node-name [state action]
  [(env/extract-context state (env/precondition-context action state)) (env/action-name action)])

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

(defn make-sequential-search [s1 s2-factory]
  
  )

(defn sa-node-name [state actions]
  [state (map env/action-name actions)])

(defn make-sp-search [state reward sol remaining-actions]
  (if-let [[f & r] (seq remaining-actions)]
    (is/make-expanding-search (sa-node-name state remaining-actions) nil reward
      (if (env/primitive? f)
        (lazy-seq 
          (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
           [(make-sp-search ss (+ reward sr) (conj sol f) r)]))
        (lazy-seq 
         (for [ref (hierarchy/immediate-refinements f state)]
           (make-sp-search state reward  sol (concat ref r))))))
    (is/make-goal-search state reward (util/prln sol))))

(defn make-incremental-dijkstra-sa-search [state action]
  (is/make-incremental-dijkstra-search (gensym) [(make-sp-search state 0 [] [action])] nil))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)
(def *problem-cache*)

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

#_ (defn sahtn-simple [henv]
  (hierarchical-search henv (constantly :recursive-exhaustive)
    (comp make-exhaustive-search make-incremental-dijkstra-sa-search)))

#_ (defn sahtn-dijkstra [henv]
  (hierarchical-search henv (if-cycle-fn :transparent :recursive-exhaustive) 
    (comp make-exhaustive-search make-incremental-dijkstra-sa-search)))


(defn sahucs-flat [henv]
  (hierarchical-search henv (constantly :transparent)
    make-incremental-dijkstra-sa-search))

#_ (defn sahucs-simple [henv]
  (hierarchical-search henv (constantly :recursive)
    make-incremental-dijkstra-sa-search))

#_ (defn sahucs-dijkstra [henv]
  (hierarchical-search henv (if-cycle-fn :transparent :recursive) 
    make-incremental-dijkstra-sa-search))

#_ (defn sahucs-inverted [henv]
  (hierarchical-search henv :dummy
    make-inverted-sa-search))



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