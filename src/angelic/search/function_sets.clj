(ns angelic.search.function-sets
  (:require
   [angelic.util :as util]
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
  (primitive? [fs]           "needed for SAHTN, etc.")
  (precondition-context-set [fs input-set] "Relevant set of variables")  
  (apply-opt  [fs input-set] "[output-set upper-reward-bound status].
       output nil if empty or -inf. Status is :live/:blocked/:solved.")
  (apply-pess [fs input-set] "[output-set upper-reward-bound status].
       output nil if empty or -inf. Status is :live/:blocked/:solved.")  
  (child-seqs [fs input-set] "seq of seqs of FunctionSets. Only valid if above is :live.
       (= :live (status fs s)) ==>
        (subset? (child-seqs fs s-subset) (child-seqs fs s)) (for names)"))

(defn extract-context [fs input-set]
  (state/extract-context input-set (precondition-context-set fs input-set)))

(defn get-logger [fs input-set]
  (state/get-logger input-set (precondition-context-set fs input-set)))

(defn apply-descs [fs [p-set o-set]]
  (let [[o-out o-rew o-stat] (apply-opt fs o-set)]
    (when o-out
      (if (and (= o-stat :solved) p-set (state-set/singleton o-set))
        [[o-out o-out] [o-rew o-rew] :solved]
        (let [[p-out p-rew p-stat] (when p-set (apply-pess fs p-set))]
          (when p-out
            (case o-stat
                  :solved (assert (= p-stat :solved))
                  :live   (assert (= p-stat :live))
                  :blocked (assert (#{:blocked :solved} p-stat))))
          [[p-out o-out]
           [(if p-out p-rew Double/NEGATIVE_INFINITY) o-rew]
           o-stat])))))

(def dead-outcome [nil Double/NEGATIVE_INFINITY :blocked])
(defn- output-or-nil [desc-fn stat-fn action input-set]
  (or (when-let [[out-set rew] (desc-fn action input-set)]
        (when (and (not (state-set/empty? out-set)) (> rew Double/NEGATIVE_INFINITY))
          [out-set rew (stat-fn input-set)]))
      dead-outcome))

(defn- make-fs [action prim? status-fn child-seq-fn]
  (let [n (env/action-name action)]
   (reify
    Object
    (hashCode [fs] (hash n))
    (equals   [fs ofs] (and (instance? angelic.search.function_sets.FunctionSet ofs)
                            (= n (fs-name ofs))))    
    FunctionSet
    (fs-name    [fs]           n)
    (primitive? [fs] prim?)
    (precondition-context-set [fs input-set]
      (angelic/precondition-context-set action input-set))
    (apply-opt  [fs input-set]
      (output-or-nil angelic/optimistic-set-and-reward status-fn action input-set))
    (apply-pess [fs input-set]
      (output-or-nil angelic/pessimistic-set-and-reward status-fn action input-set))        
    (child-seqs [fs input-set] (child-seq-fn input-set)))))

(defmethod print-method angelic.search.function_sets.FunctionSet [s o]
           (print-method (fs-name s) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implementations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-primitive-fs [action]
  (make-fs action true (constantly :solved) (fn [i] (throw (UnsupportedOperationException.)))))

;; Now requrie all pairs.
(defn- simple-immediate-refinements-set [a input-set]
  (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
    (cond (empty? ref)
          [(env-util/make-factored-primitive [:noop constraint]
            (util/map-vals util/safe-singleton constraint) {} 0)
           (env-util/make-factored-primitive [:noop] {} {} 0)]
          
          (or (= 1 (count ref)) (seq constraint))
          (cons
           (env-util/make-factored-primitive [:noop constraint]
            (util/map-vals util/safe-singleton constraint) {} 0)     
           ref)

          :else
          ref)))

(defn make-hla-fs [action]
  (make-fs action false
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
  (if (vector? henv)
    (let [[init init-fs] henv]
      [(state-set/make-logging-factored-state-set
        [(state/get-logger init (state/current-context init))])
       init-fs])    
    [(state-set/initial-logging-ss (hierarchy/env henv)) (make-tla-fs henv)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn =-state-sets [s1 s2]
  (util/assert-is (clojure.set/subset? (state/current-context s1)
                                       (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

(defn =-in-context [s1 s2]
  #_ (=-state-sets s1 s2)
  (state/equal-in-context s1 s2))

(defn map-sets [f fs [ps os]] [(when ps (f fs ps)) (f fs os)])

(defn eq-sets [pred [p1 o1] [p2 o2]]
  (and (pred o1 o2)
       (or (and (nil? p1) (nil? p2))
           (and (not (nil? p1)) (not (nil? p2)) (pred p1 p2)))))


(defn transfer-effects [to-set from-set]
  (state/transfer-effects to-set from-set))

(defn unrefinable-set? [s] (state-set/singleton-in-context? s))