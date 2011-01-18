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
  (fs-name    [fs]           "Arbitrary name to identify fs")
  (apply-opt  [fs input-set] "[output-set upper-reward-bound] or nil if empty/-inf")
  (apply-pess [fs input-set] "[output-set upper-reward-bound] or nil if empty/-inf")  
  (status     [fs input-set] ":live, :blocked, or :solved")
  (child-seqs [fs input-set] "seq of seqs of FunctionSets. Only valid if above is :live.
                              (= :live (status fs s)) ==>
                                 (subset? (child-seqs fs s-subset) (child-seqs fs s)) (for names)")
  (precondition-context-set [fs input-set] "Relevant set of variables")
  (extract-context [fs input-set] "Relevant parts of input-set, for state abstraction")
  (get-logger  [fs input-set]     "Get logger for input-set, in context of fs (also for SA)."))

(defn- output-or-nil [[opt rew :as p]]
  (when (and p (not (state-set/empty? opt)) (> rew Double/NEGATIVE_INFINITY))
    p))

(defn- make-fs [action status-fn child-seq-fn]
  (let [n (env/action-name action)]
   (reify
    Object
    (hashCode [fs] (hash n))
    (equals   [fs ofs] (and (instance? angelic.search.function_sets.FunctionSet ofs)
                            (= n (fs-name ofs))))    
    FunctionSet
    (fs-name    [fs]           n)
    (apply-opt  [fs input-set] (output-or-nil (angelic/optimistic-set-and-reward action input-set)))
    (apply-pess [fs input-set] (output-or-nil (angelic/pessimistic-set-and-reward action input-set)))        
    (status     [fs input-set] (status-fn input-set))
    (child-seqs [fs input-set] (child-seq-fn input-set))
    (precondition-context-set [fs input-set] (angelic/precondition-context-set action input-set))
    (extract-context [fs input-set]
      (state/extract-context input-set (angelic/precondition-context-set action input-set)))
    (get-logger  [fs input-set]
      (state/get-logger input-set (angelic/precondition-context-set action input-set))))))

(defmethod print-method angelic.search.function_sets.FunctionSet [s o]
           (print-method (fs-name s) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implementations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-primitive-fs [action]
  (make-fs action (constantly :solved) (fn [i] (throw (UnsupportedOperationException.)))))

(defn- simple-immediate-refinements-set [a input-set]
  (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
    (if (or (empty? ref) (seq constraint))
      (cons
       (env-util/make-factored-primitive [:noop constraint]
                                         (util/map-vals util/safe-singleton constraint) {} 0)     
       ref)
      ref)))

(defn make-hla-fs [action]
  (make-fs action
    #(if (angelic/can-refine-from-set? action %) :live :blocked)
    #(for [ref (simple-immediate-refinements-set action %)]
       (for [a ref]
         ((if (env/primitive? a) make-primitive-fs make-hla-fs) a)))))


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
