(ns angelic.search.function-sets
  (:require
   [edu.berkeley.ai.util :as util]
   [angelic.env :as env]
   [angelic.env.util :as env-util]
   [angelic.env.state :as state]               
   [angelic.hierarchy.angelic :as angelic]
         
   [angelic.hierarchy :as hierarchy]   
   [angelic.hierarchy.util :as hierarchy-util]
   [angelic.hierarchy.state-set :as state-set]   ))


;; An abstraction of HLAs and primitive actions, just for implicit for now.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Function Sets ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol FunctionSet
  (fs-name    [sk]           "Arbitrary name to identify fs")
  (apply-opt  [sk input-set] "[output-set upper-reward-bound] or nil if empty/-inf")
  (status     [sk input-set] ":live, :blocked, or :solved")
  (child-seqs [sk input-set] "seq of seqs of FunctionSets. Only valid if above is :live.
                              (= :live (status sk s)) ==>
                                 (subset? (child-seqs sk s-subset) (child-seqs sk s)) (for names)")
  (extract-context [sk input-set] "Relevant parts of input-set, for state abstraction")
  (get-logger  [sk input-set] "Relevant parts of input-set, for state abstraction"))

;; Child-seqs must obey the containment property for subsets of input-set.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implementations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn viable-or-nil [[opt rew :as p]]
  (when (and p (not (state-set/empty? opt)) (> rew Double/NEGATIVE_INFINITY))
    p))


(defn extract-context* [action input-set]
  (state/extract-context input-set (angelic/precondition-context-set action input-set)))

(defn get-logger* [action input-set]
  (state/get-logger input-set (angelic/precondition-context-set action input-set)))

(defn make-primitive-fs [action]
  (reify
   FunctionSet
   (fs-name    [sk]           (env/action-name action))
   (apply-opt  [sk input-set] (viable-or-nil (angelic/optimistic-set-and-reward action input-set)))
   (status     [sk input-set] :solved)
   (child-seqs [sk input-set] (throw (UnsupportedOperationException.)))
   (extract-context [sk input-set] (extract-context* action input-set))
   (get-logger  [sk input-set] (get-logger* action input-set))   
   ))

(defn- simple-immediate-refinements-set [a input-set]
  (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
    (if (or (empty? ref) (seq constraint))
      (cons
       (env-util/make-factored-primitive [:noop constraint]
                                         (util/map-vals util/safe-singleton constraint) {} 0)     
       ref)
      ref)))


(defn make-hla-fs [action]
  (reify
   FunctionSet
   (fs-name [sk] (env/action-name action))
   (apply-opt [sk input-set] (viable-or-nil (angelic/optimistic-set-and-reward action input-set)))
   (status  [sk input-set] (if (angelic/can-refine-from-set? action input-set) :live :blocked))
   (child-seqs [sk input-set]
     (for [ref (simple-immediate-refinements-set action input-set)]
       (for [a ref]
         ((if (env/primitive? a) make-primitive-fs make-hla-fs) a))))
   (extract-context [sk input-set] (extract-context* action input-set))
   (get-logger  [sk input-set] (get-logger* action input-set))   ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Constructor ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assume positive costs.
(defn make-tla-fs [henv]
  (make-hla-fs
   (hierarchy-util/make-top-level-action
    (hierarchy/env henv)
    [(hierarchy/initial-plan henv)]
    0)))

(defn make-init-pair [henv]
  [(state-set/initial-logging-ss (hierarchy/env henv)) (make-tla-fs henv)])
