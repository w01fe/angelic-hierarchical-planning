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
  (:import  [java.util HashMap]))


;; Revamp of fah_astar, try to unify the whole mess ! 
;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Much copied from previous ipmlicit-dash-a*.

;; TODO: note pseudo-RBFS potential prloblem.


;; Refinements all have at least one action, constraints are new primitives.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
