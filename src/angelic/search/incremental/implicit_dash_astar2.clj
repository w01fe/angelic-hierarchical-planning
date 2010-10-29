(ns angelic.search.incremental.implicit-dash-astar2
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [clojure.contrib.core :as ccc]
            [angelic.env :as env]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is]
            [angelic.search.incremental.summary :as summary]
            [angelic.search.incremental.summaries :as summaries]
            [angelic.search.incremental.lattices :as lattices]                        
            )
  (:import  [java.util HashMap IdentityHashMap]))


;; Revamp of fah_astar, try to unify the whole mess ! 
;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Much copied from previous ipmlicit-dash-a*.

;; TODO: note pseudo-RBFS potential prloblem.

;; TODO: need some superstructure to take into account initial 0-reward bound.

;; Some ideas to simplify for now:
;; - assume we always evaluate supers first
;; - suppose refs have at least one action?
;; - suppose constraints are modified to be primitives
;; - suppose all refinements have length 2? 

;; Note: if we want to be able to drive entirely from separate summaries,
;; action can't keep track of pending input sets -- this must happen
;; in ActionInRefinement. ?
;; But, this means we have to notice when action becomes unblocked?  maybe ok
;; Refinements keep a watch on input sets
;; Following nodes keep watch on ??

;; WrappedLattice -- maintains node-by-node connection
;; ActionInRefinement input is simple delta-wrapper of previous input
;; OutputLattice of action watches OutputLattices of final AIRs ?
;; OutputLattice of AIR is contextifying wrapper of sub-output.
;; Only remaining question is how to collect final outputs.
;; Options: actually connect them,
;; Or just provide a mechanism to add watchers to all.



;; ActionInstance
;;  - InputLattice - maps input sets to OutputLattices

;; ActionInstanceInContext
;;  - InputLatticeWrapper - maps input sets to OutputLatticeWrappers

;; Eval = expand InputLattice, creating corresponding OL?

;; Every action implicitly exists, with InputLattice mapping top to top, ....
;; single AIIC dummy as stand-in for refinements, blocked.

;; Op: AddInputSubset(AI, Parent, Child) -- just adds to IL, evaluates.
;; AIIC can pick up new input, gives a new target.  
;; (only allowed when Parent is already Blocked).  



;; Basic idea: stop at eval of AI, for now.

;; When we eval, we produce refinements, plus output.
;; Suppose all refinements have length 2.  
;; Then we have 2 phases -- first refining of each, then splitting -- over tree at middle.

;; ActionInstance is truly independent, made to be shared. 
;; It has single input set, output lattice,

;; Not really clear what the point of the InputLattice is for now --
;; OK, do simple factored version first, no sharing or state abstractino ?

;; Still have correspondence problem from before?
;; In particular, say we only care about one particular output.
;; How does this propagate back ?

;; This should be a proper lattice?
;; But this requires rethinking everything; multiple parents, etc.
;; Each AIIC watches output lattices as added.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def +top-set+ :dummy)
;(def ^HashMap *ai-cache* nil)

(defn optimistic-set-and-reward-top [action input-set]
  (if (identical? input-set +top-set+)
    [+top-set+ 0]
    (angelic/optimistic-set-and-reward action input-set)))

(defn can-refine-from-set-top? [action input-set]
  (and (not (identical? input-set +top-set+))
       (angelic/can-refine-from-set? action input-set)))


(declare make-action-instance-in-context)

(defrecord ActionInstance
  [action
   input-lattice-root ; maps input set to output lattice -- root is always top
   ])


(defn make-ai-refinement-watcher [action]
  (fn watcher [parent-node new-child-node]
    (let [input-set      (lattices/node-key new-child-node)]
      (if (angelic/can-refine-from-set? action input-set)
        (doseq [[constraint ref] (angelic/immediate-refinements-set action input-set)]
          (make-action-instance-in-context new-child-node constraint ref))
        (lattices/add-watcher! new-child-node watcher)))))

(defn make-action-instance [action parent-input-lattice-root]
  (let [my-root (lattices/make-transformed-lattice
                 parent-input-lattice-root
                 node-key
                 #(lattices/make-lattice-node 
                   nil nil (first (optimistic-set-and-reward-top action (node-key %)))
                   nil))]
    (when-not (env/primitive? action) (lattices/add-watcher! my-root (make-ai-refinement-watcher action)))  
    (ActionInstance. action my-root)))


(defrecord ActionInstanceInContext
  [input-lattice-root ; already evaluated pairs
   pending-leaves     ; [parent input-set] pairs, with constraints applied
   sub-ai
   ])

(defn make-initial-output-lattice [] (lattices/make-lattice-node nil nil +top-set+ nil))
(defn make-initial-input-lattice []
  (lattices/make-lattice-node nil nil +top-set+ (make-initial-output-lattice)))

;; TODO: constraint
(defn make-action-instance-in-context [input-root constraint action]
  (let [pending-leaves (IdentityHashMap.)
        my-root        (make-initial-input-lattice)]
    (ActionInstanceInContext. my-root pending-leaves (make-action-instance action my-root))))

(defn evaluate-pending-pair! [aiic [parent-node input-set :as pending]]
  (let [pending-leaves ^IdentityHashMap (:pending-leaves aiic)]
    (assert (.containsKey pending-leaves pending))
    (.remove pending-leaves pending)
    (lattices/add-child! parent-node input-set (make-initial-output-lattice))))


(defn make-refinement [input-lattice constraint remaining-actions final-output-lattice]
  (if (empty? remaining-actions)
    (start-copy input-lattice final-output-lattice)
    (let [first-aiic (make-action-instance-in-context input-lattice constraint (first remaining-actions))]
      (make-refinement ... {} (next remaining-actions) final-output-lattice))))

;; How do lattices get mashed ? 







(comment
  (defn make-contextualized-output-lattice [output-lattice context]
  (lattices/make-transformed-lattice
   output-lattice
   (fn [output-node] (state/transfer-effects context (lattices/node-key output-node)))
   (fn [output-node] (assert (not (lattices/node-data output-node)))))))

(comment     (lattices/add-watcher! prev-output-lattice
     (make-lattice-node-watcher (fn [parent-node child-node] (.add pending-leaves [parent-node child-node])))))


(comment 
 (defrecord LatticeNode
   [input-set
    child-map])

 (defrecord OutputLatticeNode
   [output-set
    child-map])

 (defrecord Action
   [a
    input-lattice-root])

 (defrecord ActionInRefinement
   [sub-action
    input-set->output-lattice
    input-lattice
    pending-inputs ;; eventually gone
    final-output-set
    input->output-   
    ])

 (defrecord ActionInstance
   [parent-ai
    super-ais
    prev-aio
    actions                        ; this and following in refinement.
    output-atom ])

 (defrecord ActionInstanceOutput
   [parent-aio                          ; Only if no more actions
    super-aios                          ; 
    source-ai
    output-set
    step-reward
    next-ai-atom
    refinents-first-ai-atom])

 (def +worst-aio+ (ActionInstanceOutput. nil nil nil state-set/empty-lfss is/neg-inf nil nil))

 (defn make-constraint-primitive [constraint]
   (env-util/make-factored-primitive [:noop] constraint {} 0))

 (defn root-aio [aio]
   (if-let [parent (:parent-aio aio)] (root-aio parent) aio))



 (defn evaluate-aio! [ai]
   (let [{:keys [parent-ai super-ais prev-aio actions output-atom]} ai]
     (assert (nil? @output-atom))
     (let [input-set (:output-set prev-aio)
           [a & r]   actions
           prim?    (env/primitive? a)
           [opt rew] (angelic/optimistic-set-and-reward a input-set)]
       (if (or (not opt) (state-set/empty? opt) (= rew is/neg-inf))
         +worst-aio+
         (let [aio (ActionInstanceOutput.
                    (when (empty? r) (-> parent-ai :output-atom deref))
                    (ccc/-?> super-ai :output-atom deref)
                    ai opt rew
                    (atom nil) (atom nil))]
           (reset! (:refinements-first-ai-atom aio)
                   (lazy-seq
                     (let [super-fais (ccc/-?> aio :super-aio :refinements-first-ai-atom)]
                       (cond (and @super-fais (not (= @super-refs :blocked)))
                             (for [super-fai @super-fais]
                               (ActionInstance. ai super-fai prev-aio (:actions super-fai) (atom nil)))
                             (angelic/can-refine-from-set? a input-set)
                             (for [[constraint ref] (angelic/immediate-refinements-set a input-set)
                                   :let [full-ref (cons (make-constraint-primitive constraint) ref) ]]
                               (ActionInstance. ai nil prev-aio full-ref (atom nil)))
                             :else
                             :blocked))))
           (reset! (:next-ai-atom aio)
                   (let [root (root-aio aio)]
                     (ActionInstance.
                      (-> root :source-ai :parent-ai)
                      (if (identical? aio root) ;; AKA this AIO has more actions
                        (ccc/-?> ai :super-ai :output-atom deref :next-ai-atom deref)
                       
                        )
                      aio (-> root :source-ai :actions next) (atom nil))))))))))



;; MAke a special finish that cannot be evaluated.
;; Now, can start with all unevaluated actions (ends of the line). Push reward back, up to parentAI, down to subs.
;; This leaves out pushing down refs.  Allows to "fill in" for unevaluated refs. That would be unnec. with superstructure?
;; Problem: how do we determine current best bound? 
