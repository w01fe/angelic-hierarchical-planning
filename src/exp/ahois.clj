(ns exp.ahois
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy]
            [exp.incremental-search :as is])
  (:import  [java.util HashMap]))


; Angelic hierarchy of optimal incremental searches

;; TODO: fix paredit key bindings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Forward Search Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-forward-search-node [actions-fn goal-fn state reward opt-sol]
  (is/SimpleNode state reward (if (goal-fn state) opt-sol)       
    (lazy-seq
     (for [a (actions-fn state)
           :when (env/applicable? a state)
           :let  [[ss r] (env/successor a state)]]
       (make-forward-search-node actions-fn goal-fn ss (+ reward r) (conj opt-sol a))))))

(defn make-forward-search-root-node [env]
  (make-forward-search-node (env/actions-fn env) (env/goal-fn env) (env/initial-state env) [] 0))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype HierarchicalForwardState [state reward opt-sol remaining-actions])

(defn hfs-name [hfs]
  [(:state hfs) (map env/action-name (:remaining-actions hfs))])

(defn make-root-hfs [state action]
  (HierarchicalForwardState state 0 [] [actions]))

(defn next-hfs-prim [state reward opt-sol prim-action more-actions]
  (when-let [[ss sr] (and (env/applicable? prim-action state) 
                          (env/successor prim-action state))]
    [(HierarchicalForwardState state (+ reward sr) (conj opt-sol action) more-actions)]))

(defn next-hfs-expand [state reward opt-sol hla more-actions]
  (for [ref (hierarchy/immediate-refinements hla state)]
    (HierarchicalForwardState state reward opt-sol (concat ref more-actions ))))

(defn next-hfs-flat [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs
        [f & r] remaining-actions]      
    ((if (env/primitive? action) next-hfs-prim next-hfs-expand)
     state reward opt-sol f r)))

(defn hfs->simple-node [hfs]
  (if (empty? (:remaining-actions hfs))
    (SimpleNode (hfs-name hfs) (:reward hfs) (:opt-sol hfs) nil hfs)
    (SimpleNode (hfs-name hfs) (:reward hfs) nil (lazy-seq (map hfs->simple-node (next-hfs-flat hfs))) hfs)))

(defn lift-hfs 
  "Lift child-solution into the context of parent-node."
  [parent child-solution]
    (assert (is/solution child-solution))
    (HierarchicalForwardState
     (env/apply-effects (:state parent)   (env/extract-effects (:state child-solution)))
     (+                 (:reward parent)  (:reward child-solution))
     (concat            (:opt-sol parent) (:opt-sol child-solution))
     (next (:remaining-actions parent))))


(defn sa-node-name 
  ([state action] (sa-node-name state action (env/precondition-context action state)))
  ([state action context] [(env/extract-context state context) (env/action-name action)]))

(defn drop-hfs
  "Construct first abstracted name & fn returning hfs subproblem, counterpart to lift."
  [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs
        [f & r] remaining-actions
        context (env/precondition-context f state)]      
    [(sa-node-name state f context)
     (make-root-hfs (env/get-logger state context) f)]))

(defn onionize)

(defn abstract-hfs [hfs])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here, solution are solutions, and we break apart the hfs each time.


(defn make-simple-flat-search [state action]
  (make-flat-incremental-dijkstra [(hfs->simple-node (make-root-hfs state action))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; slower, using recursive search doodad.  If we allowed searchify to return list of nodes,
; could avoid nonsense here.

; Nonsense is: to expand node, we create a search whose goals are its flat refinements.
; To lift these, we just extract the goals.

(defn make-flat-search  [state action]
  (make-recursive-incremental-dijkstra
   ??? (hfs->simple-node (make-root-hfs state action)) 
   (fn [n] [(make-flat-incremental-dijkstra (map make-meta-goal-node (expand n))) solution])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-rhs-node)

; wasteful?


; Almost - how do we get context of solution node to lift it?
 ; Either need yet another abstraction (like search, but can return non-goal);
 ; Or child keeps track of context (breaks state abstraction)
 ; Or RID keeps track of search, lift-fn pairs -- Fine, have to 



(defn lift-solution-node [parent-hfs child-node]
  (make-recursive-node (lift-hfs parent-hfs (is/solution child-node)))) 

;; TODO: is data safe across state abstraction ?
;; TODO: recursive recursively is where polymorphism fits in.
(defn recursively-searchify-hfs [hfs]
  (let [[name abstract-hfs-fn] (drop-hfs hfs)]
    [(is/get-cached-search *problem-cache* name
       (let [child-hfs (abstract-hfs-fn)]
         (make-recursive-incremental-dijkstra
          ???-root (hfs->simple-node (next-hfs-flat hfs)) (comp recursively-searchify-hfs :data))))
     #(lift-solution-node hfs %)]))

(defn make-recursive-search [state action]
  (first (recursively-searchify-hfs (make-root-hfs state action))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)

(defn hierarchical-search [henv policy search-maker]
  (binding [*node-type-policy* policy
            *problem-cache*    (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (search-maker init tla)]
      (when-let [sol (is/next-goal-node top Double/NEGATIVE_INFINITY)]
        (assert (is/solution sol))
        [(map identity #_env/action-name (is/solution sol)) (is/max-reward sol) ]))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Drivers   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn sahucs-flat [henv]
  (hierarchical-search henv nil (comp  make-hfs-root-node)))

(defn sahucs-simple [henv]
  (hierarchical-search henv nil
    #(make-flat-incremental-dijkstra (make-hfs-node %1 0 [] [%2]))))














(comment 

  (deftype HierarchicalRecursiveSeqNode [name state reward opt-sol remaining-actions]
    Comparable (compareTo  [x] (- (max-reward x) reward))
    is/Summary (max-reward [] reward)
    (solution   [] (if (empty? remaining-actions) opt-sol))   
    is/Node    (node-name  [] name)
    (expand     []
                (when-let [[f & r] (seq remaining-actions)]
                  (if (env/primitive? f)
                    (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
                      (make-hfs-node ss (+ reward sr) (conj opt-sol f) r))
                    (for [ref (hierarchy/immediate-refinements f state)]
                      (make-hfs-node state reward opt-sol (concat ref r))))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchical Search Node ;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype HierarchicalNode [state action]
  Comparable
   (compareTo [x] (- (max-reward x) reward))
  is/Summary
   (max-reward [] reward)
   (is-goal?   [] (goal-fn state))  
  is/Node
   (node-name [] state)
   (expand    []
     (for [a (actions-fn state)
           :when (env/applicable? a state)
           :let  [[ss r] (env/successor a state)]]
       (ForwardSearchNode. actions-fn goal-fn ss (conj opt-sol a) (+ reward r)))))

(defn make-forward-search-root-node [env]
  (ForwardSearchNode (env/actions-fn env) (env/goal-fn env) (env/initial-state env) [] 0))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;











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

(def *node-type-policy* (fn [state first-action] :unknown))

(defn sa-node-name 
  ([state action] (sa-node-name state action (env/precondition-context action state)))
  ([state action context] [(env/extract-context state context) (env/action-name action)]))

(defn make-node-descendant [root goal-node remaining-actions] 
  (assert (is/optimal-solution goal-node))
  (if-let [[f & r] (seq remaining-actions)]
    ((*node-type-policy* root [goal-node f]) root goal-node remaining-actions)
    goal-node))

(defn sp-node-name [state actions]
  [state (map env/action-name actions)])

(defn next-goal [start-node prim-action]
  (let [state (is/goal-state start-node)]
    (when-let [[ss sr] (and (env/applicable? prim-action state) (env/successor prim-action state))]
      (is/make-goal-search ss (+ is/max-reward start-node sr)
                           (conj (is/optimal-solution start-node) prim-action)))))

(defn sa-children 
  "Compute children (refinements or result) of action from state.  Return a list of
   [next-node remaining-action' pairs."
  [start-node action]
  (lazy-seq
   (if (env/primitive? action)
     (result-fn (next-goal start-node action) nil)
     (for [ref (hierarchy/immediate-refinements action (is/goal-state start-node))]
       (result-fn start-node ref)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Straight search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn next-transparent-node [root goal-node [f & r :as remaining-actions]]
  (is/make-expanding-search 
   (sp-node-name (is/goal-state goal-node) remaining-actions) nil (is/max-reward goal-node)
   (for [[n ref] (sa-children goal-node f)] (make-node-descendant root n (concat ref r)))))

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
    (is/make-transformed-search 
     (sp-node-name state remaining-actions)
     (is/get-cached-search *problem-cache* in-name
       (make-incremental-dijkstra-sa-search in-name (env/get-logger state context) f))
     #(make-node-descendant root (contextualize-goal goal-node %) r)
     (is/max-reward goal-node)
     nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Spse we have two different paths to same sps
; Do we have to reify sps as separate OR-searches? No guaranteed ijkstra structure here so ...

; Note: either creation must be eager, OR sasps must be smarter.

;; Now, ?? ? ? ??
 ; Issue: we really want SA-node + wrapper ? 

(declare make-saha-sasps-node)

(defn make-saha-sps-node [start-node remaining-actions final-state]
  (if-let [[f & r] (seq remaining-actions)]
    (let [state (is/goal-state start-node)
          name  [state (map env/action-name remaining-actions) final-state]]
      (is/get-cached-search *problem-cache* name
        (make-incremental-dijkstra-search name
          (let [next-children (sa-children start-node f)]
            (for [[ss sr] (env/optimistic-map next-action state)] 
              (make-saha-sasps-node start-node f ss sr r final-state next-children)))
          final-state)))
    start-node))

(defn make-saha-sas-node 
  ([start-node action final-state]
     (make-saha-sas-node start-node action final-state ref-seq)
     )
  ([start-node action final-state opt-reward next-children]
     (let [state   (is/goal-state start-node)
           context (env/precondition-context action state)
           log-state (env/get-logger state context)
           in-name (sa-node-name state f context)]
       (is/make-transformed-search (gensym)
         (is/get-cached-search *problem-cache* in-name
           (make-incremental-dijkstra-search in-name 
             (for [[n ref] ref-seq] )
             (lazy-seq
              (if (env/primitive? f)
                (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
                  [(make-node-descendant root 
                     (is/make-goal-search ss (+ (is/max-reward goal-node) sr) 
                                          (conj (is/optimal-solution goal-node)  f)) r)])
                (for [ref (hierarchy/immediate-refinements f state)]
                  (make-node-descendant root goal-node (concat ref r)))))
             final-state))
         #(make-node-descendant root (contextualize-goal goal-node %) r) ;; TODO...
         (is/max-reward goal-node)
         nil)))
   
  (is/make-transformed-search 
     (sa-node-name state actions)
     (is/get-cached-search *problem-cache* in-name
       (make-incremental-dijkstra-sa-search in-name (env/get-logger state context) f))
     #(make-node-descendant root (contextualize-goal goal-node %) r)
     (is/max-reward goal-node)
     nil))

(defn make-saha-sasps-node [start-node action med-state med-reward remaining-actions final-state refs]
  (let [sas      (make-saha-sas-node start-node action med-state med-reward refs)
        med-node (is/make-goal-search med-state med-reward nil) ])
  (if (empty? remaining-actions) sas  ;; just for efficiency, could be removed.
    (is/make-closed-sequence-search 
     (gensym) sas 
     (make-saha-sps-node med-node remaining-actions final-state)
     (fn [a b] a))))

(defn make-saha-sas-node 
  ([start-node action final-state]
     (make-saha-sas-node start-node action final-state ref-seq)
     )
  (let [state   (is/goal-state start-node)
        context (env/precondition-context action state)
        log-state (env/get-logger state context)
        in-name (sa-node-name state f context)]
    (is/make-transformed-search (gensym)
     (is/get-cached-search *problem-cache* in-name
       (make-incremental-dijkstra-search in-name 
         (lazy-seq
          (if (env/primitive? f)
            (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
              [(make-node-descendant root (is/make-goal-search ss (+ (is/max-reward goal-node) sr) 
                                                               (conj (is/optimal-solution goal-node)  f)) r)])
            (for [ref (hierarchy/immediate-refinements f state)]
              (make-node-descendant root goal-node (concat ref r)))))
         final-state))
     #(make-node-descendant root (contextualize-goal goal-node %) r) ;; TODO...
     (is/max-reward goal-node)
     nil))
   
  (is/make-transformed-search 
     (sa-node-name state actions)
     (is/get-cached-search *problem-cache* in-name
       (make-incremental-dijkstra-sa-search in-name (env/get-logger state context) f))
     #(make-node-descendant root (contextualize-goal goal-node %) r)
     (is/max-reward goal-node)
     nil))

(defn make-saha-sa-node [root goal-node remaining-actions outcome-state opt-rew]
  (if-let [[f & r] (seq remaining-actions)]
    ((*node-type-policy* root [goal-node f]) root goal-node remaining-actions)
    goal-node)

  )

(defn make-saha-sa-node [root goal-node next-action]
  (let [state (is/goal-state goal-node)]
    (is/make-expanding-search (sa-node-name state next-action) nil (is/max-reward goal-node)
      (lazy-seq 
       (for [[s r] (env/optimistic-map next-action state)]
         (make-saha-refinement-node root goal-node next-action s r))))))



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