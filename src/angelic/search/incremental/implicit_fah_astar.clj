(ns angelic.search.incremental.implicit-fah-astar
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
;            [angelic.search.incremental.summaries :as summaries]
            )
  (:import  [java.util HashMap]))


;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Much copied from previous ipmlicit-dash-a*.

;; TODO: note pseudo-RBFS potential prloblem.

; ;What connection, if any, do pessimistic need with optimistic?  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Function Sets ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol FunctionSet
  (fs-name    [sk]           "Arbitrary name to identify fs")
  (apply-opt  [sk input-set] "[output-set upper-reward-bound] or nil if empty")
  (status     [sk input-set] ":live, :blocked, or :solved")
  (child-seqs [sk input-set] "seq of seqs of FunctionSets. Only valid if above is :live.
                              (= :live (status sk s)) ==>
                                 (subset? (child-seqs sk s-subset) (child-seqs sk s)) (for names)"))

;; Child-seqs must obey the containment property for subsets of input-set.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning Kernels ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-primitive-fs [action]
  (reify FunctionSet
    (fs-name    [sk]           (env/action-name action))
    (apply-opt  [sk input-set] (angelic/optimistic-set-and-reward action input-set))
    (status     [sk input-set] :solved)
    (child-seqs [sk input-set] (throw (UnsupportedOperationException.)))))

(defn- simple-immediate-refinements-set [a input-set]
  (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
    (cons
     (env-util/make-factored-primitive [:noop] constraint {} 0)     
     ref)))

(defn make-hla-fs [action]
  (reify FunctionSet
         (fs-name [sk] (env/action-name action))
         (compute-output-set-and-reward   [sk input-set]
            (angelic/optimistic-set-and-reward action input-set))
         (compute-status   [sk input-set]
            (if (angelic/can-refine-from-set? action input-set) :live :blocked))
         (compute-child-fs-seqs [sk input-set child-key]
            (for [ref (simple-immediate-refinements-set action input-set)]
              (for [a ref]
                ((if (env/primitive? action) make-primitive-fs make-hla-fs) action))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For now, go with simple "complete eval" formulation.
;; Will have "atomic" and "seq" subproblems -- separate impls..

(def no-children :terminal)

(defprotocol Subproblem
  (input-set       [s])
  (output-set      [s])
;  (current-summary [s])
  (child-keys      [s] "seq or no-children")
  (get-child       [s child-key])
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))

(defn refine-input [s maybe-refined-input-set]
  (if (= (input-set s) maybe-refined-input-set)
    s
    (refine-input- s maybe-refined-input-set)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simple FS Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Very simple, no caching or reuse or anything.

(declare make-simple-fs-seq-subproblem)

(defn make-simple-atomic-subproblem [inp-set function-set]
  (let [out-set (apply-opt function-set inp-set)
        stat    (fs-status function-set)
        fs-child-seqs (when (= stat :live) (child-seqs function-set inp-set))
        fs-child-seqs-map (zipmap (map #(map fs-name %) fs-child-seqs) fs-child-seqs)]
    (assert (= (count fs-child-seqs-map) (count fs-child-seqs))) 
    (reify
     Subproblem
     (input-set       [s] inp-set)
     (output-set      [s] out-set)
     (child-keys      [s] (if (= stat :live) (keys fs-child-seqs-map) no-children))
     (get-child       [s child-key]
       (->> (util/safe-get fs-child-seqs-map child-key)
            (make-simple-factored-seq-subproblem inp-set)))
     (refine-input    [s refined-input-set]
       (make-simple-atomic-subproblem refined-input-set function-set)))))


;; NOTE: If we require that input and output match always, we just get back AHA*.
;; (but with UP, perhaps caching?).


(declare make-simple-pair-subproblem)

(defn make-aligned-simple-pair-subproblem [sp1 sp2]
  (make-simple-pair-subproblem sp1 (refine-input sp2 (output-set sp1))))

(defn simple-pair-child-keys [sp1 sp2]
  (let [sp2-child-keys (child-keys sp2)]
    (if (= sp2-child-keys no-children)
      (let [sp1-child-keys (child-keys sp1)]
        (if (= sp1-child-keys no-children)
          no-children
          (map #(vector ::1 %) sp1-child-keys)))
      (map #(vector ::2 %) sp2-child-keys))))

(defn simple-pair-child [sp1 sp2 child-key]
  (let [[which sub-key] child-key]
    (case which
      ::1 (make-aligned-simple-pair-subproblem (get-child sp1 sub-key) sp2)
      ::2 (make-simple-pair-subproblem sp1 (get-child sp2 sub-key)))))


(defn make-simple-pair-subproblem [sp1 sp2]
  (let [child-keys (simple-pair-child-keys sp1 sp2)]
    (reify
     Subproblem
     (input-set       [s] (input-set sp1))
     (output-set      [s] (output-set sp2))
     (child-keys      [s] child-keys)
     (get-child       [s child-key] (simple-pair-child sp1 sp2 child-key))
     (refine-input    [s refined-input-set]
       (make-aligned-simple-pair-subproblem (refine-input sp1 refined-input-set) sp2)))))

(defn make-simple-fs-seq-subproblem [inp-set [first-fs & rest-fs]]
  (let [first-sp (make-simple-atomic-subproblem inp-set first-fs)]
    (if (empty? rest-fs)
      first-sp
      (->> (make-simple-fs-seq-subproblem (output-set first-sp) rest-fs)
           (make-simple-pair-subproblem first-sp)))))






(comment ; old version- has some caching.
 (defn make-simple-atomic-subproblem [inp-set function-set]
   (let [child-cache (HashMap.)
         refinement-cache (HashMap.)
         out-set (apply-opt function-set inp-set)
         fs-child-seqs (child-seqs function-set inp-set)
         fs-child-seqs-map (zipmap (map #(map fs-name %) fs-child-seqs) fs-child-seqs) ]
     (assert (= (count fs-child-seqs-map) (count fs-child-seqs))) 
     (reify
      Subproblem
      (input-set       [s] inp-set)
      (output-set      [s] out-set)
      (child-keys      [s] (keys fs-child-seqs-map))
      (get-child       [s child-key]
                       (->> (util/safe-get fs-child-seqs-map child-key)
                            (make-simple-factored-seq-subproblem inp-set)
                            (util/cache-with child-cache child-key)))
      (refine-input    [s refined-input-set]
                       (make-simple-atomic-subproblem refined-input-set function-set))))))

(declare make-generic-subproblem)

(defrecord GenericSubproblem [; ??? summarizer
                              kernel in-set out-set child-key-seq
                              ^HashMap child-cache ^HashMap refinement-cache]
  (input-set       [s] in-set)
  (output-set      [s] out-set)
  (current-summary [s] ...???)
  (child-keys      [s] child-key-seq)
  (get-child       [s child-key]
    (util/cache-with child-cache child-key (compute-child-kernel kernel in-set child-key)))
  (refine-input    [s refined-input-set]
    (if (= in-set refined-input-set)
      s
      (util/cache-with refinement-cache refined-input-set
                       (make-generic-subproblem kernel refined-input-set)))))

(defn make-generic-subproblem [kernel input-set]
  (GenericSubproblem.
   kernel
   input-set
   (compute-output-set kernel input-set)
   (compute-child-keys kernel input-set)
   (HashMap.) (HashMap.)))



;;;;;;;;;;;;;;;;;;;;;;;;;;; TopDown FS Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add caching, exploitation of subsumption, but no graphiness 





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simple Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Problem we run into here: splitting into plans without factored costs
;; = potentially very expensive queue mgmt.

;; Planning is defined only on Summarizer + a refinement operation.


(defprotocol )




;;Can forget about sets -- switch to breakout children instead.

;; Things:
;; Action - Input - Output
;; ActionSeq - Input
;; RestrictedActionSeq

;; How does all this change if leaves are leaves?
;; Restricting input
;; Where do the breaks go?
;; Operation always =
;; "expand 'first' or 'rest' of seq". ?
;; expanding on the right should be automatic ?
;; What if thing already has children?
;; Not allowed to expand on the left until right is blocked?
;; But this forces right-to-left spliting ?

;; Think about this as subproblems, partial solutions.
;; How do we handle case where subproblem is union, refined-output can grow over time ?
;; Why did we need that nonsense anyway? ...
;; ((can we get graphiness in another way?))
;; ((what if we just allow cost decrease -- so waht ? ))
;; Need lattice -- but it can be on the input side. 

(def no-children :terminal)

(defprotocol Subproblem
  (input-set       [s])
  (output-set      [s])
  (current-summary [s])
  (child-keys      [s] "seq or no-children")
  (get-child       [s child-key])
  (refine-input    [s refined-input-set]))

;;(def input-set :input-set)
;;(def output-set :output-set)
;;(defn get-child-map [s] (into {} (for [k (child-keys s)] [k (get-child s k)])))





;; TODO: getting child from super ...
(declare make-generic-subproblem)

(defrecord GenericSubproblem [; ??? summarizer
                              kernel in-set out-set child-key-seq
                              ^HashMap child-cache ^HashMap refinement-cache]
  (input-set       [s] in-set)
  (output-set      [s] out-set)
  (current-summary [s] ...???)
  (child-keys      [s] child-key-seq)
  (get-child       [s child-key]
    (util/cache-with child-cache child-key (compute-child-kernel kernel in-set child-key)))
  (refine-input    [s refined-input-set]
    (if (= in-set refined-input-set)
      s
      (util/cache-with refinement-cache refined-input-set
                       (make-generic-subproblem kernel refined-input-set)))))

(defn make-generic-subproblem [kernel input-set]
  (GenericSubproblem.
   kernel
   input-set
   (compute-output-set kernel input-set)
   (compute-child-keys kernel input-set)
   (HashMap.) (HashMap.)))




(declare make-generic-wrapping-subproblem)

(defrecord GenericWrappingSubproblem [super-sp root-sp key-trail ; summarizer???
                                      kernel in-set out-set child-key-seq
                                      ^HashMap child-cache ^HashMap refinement-cache]
  Subproblem
  (input-set       [s] in-set)
  (output-set      [s] out-set)
  (current-summary [s] ...???)
  (child-keys      [s] child-key-seq)
  (get-child       [s] ???)
  (refine-input    [s refined-input-set]
    (if (= in-set refined-input-set)
      s
      (util/cache-with refinement-cache refined-input-set
                       ???))))

(defn make-generic-subproblem [name super-sp root-sp key-trail summary???
                               in-set .....])


(defn make-refinement-kernel [actions]
  (let [[f & r] (util/make-safe actions)
        left-k (make-action-kernel f)]
    (if (empty? r)
      left-k
      (make-seq-kernel left-k (make-refinement-kernel r)))))

;; TODO: simple generic SimpleSubproblem record ? 

;; TODO: stop early on empty sets or bad rewards, etc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning Kernels ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-primitive-subproblem)
(declare make-hla-subproblem)
(declare make-atomic-subproblem)
(declare make-seq-subproblem)
(declare make-wrapper-subproblem)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitive ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-primitive-kernel [action]
  (reify SubproblemKernel
         (compute-output-set-and-reward   [sk input-set]
            (angelic/optimistic-set-and-reward action input-set))
         (compute-child-keys   [sk input-set]
            no-children)
         (compute-child-kernel [sk input-set child-key]
            (throw (UnsupportedOperationException.)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HLA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn simple-immediate-refinements-set [a input-set]
  (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
    (cons
     (env-util/make-factored-primitive [:noop] constraint {} 0)     
     ref)))

(defn make-refinement-kernel [actions]
  (let [[f & r] (util/make-safe actions)
        left-k (make-action-kernel f)]
    (if (empty? r)
      left-k
      (make-seq-kernel left-k (make-refinement-kernel r)))))

;; TODO: handle proper key matching ? 
(defn make-hla-kernel [action]
  (reify SubproblemKernel
         (compute-output-set-and-reward   [sk input-set]
            (angelic/optimistic-set-and-reward action input-set))
         (compute-child-keys   [sk input-set]
            (simple-immediate-refinements-set action input-set))
         (compute-child-kernel [sk input-set child-key]
            (make-refinement-kernel child-key))))

(defn make-action-kernel [action]
  ((if (env/primitive? action) make-primitive-kernel make-hla-kernel) action))


(comment 
  (defn make-hla-subproblem [super-hs input-set action]
    (let [[opt-set rew] (angelic/optimistic-set-and-reward action input-set)]
      (HlaSubproblem.
       super-hs input-set action opt-set ??????summarizer
       (cond (not (angelic/can-refine-from-set? action input-set))
             no-children
             (and super-hs (not (blocked??? super-hs)))
             ???                        ;reuse
             :else
             (into {}
                   (for [ref (simple-immediate-refinements-set action input-set)]
                     [(map env/action-name ref)
                      (delay (make-refinement-subproblem this??? input-set ref))
                      (ActionInstance. ai nil prev-aio full-ref (atom nil))])))
       (HashMap.)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Sequence ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-seq-kernel [left-k right-k]
  (reify SubproblemKernel
         (compute-output-set-and-reward   [sk input-set]
            (angelic/optimistic-set-and-reward action input-set))
         (compute-child-keys   [sk input-set]
            (simple-immediate-refinements-set action input-set))
         (compute-child-kernel [sk input-set child-key]
            (make-refinement-kernel child-key))))


(comment

 ;; For now, pick the right first if possible -- fix later.
 ;; TODO: unfactor ?
 ;; TODO: how do we wrap partial SPs? 
 (defrecord SeqSubproblem [super-sp root-hs key-seq
                           input-set left-sp right-sp output-constraint
                           child-map]
   Subproblem
   (current-summary [s] ...?)
   (child-keys      [s] (keys child-map))
   (get-child       [s child-key] (force (util/safe-get child-map child-key)))
   (refine-input    [s refined-input-set]
                    (if (= refined-input-set input-set)
                      s
                      (util/cache-with refinement-map refined-input-set
                                       (make-hla-subproblem s refined-input-set action)))))


 (defn make-seq-subproblem [super-sp root-hs key-seq]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Wrapped Seq ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord WrappedSubproblem [input-set wrapped-sp remaining-keys output-set]
  Subproblem
  (current-summary [s] ...)
  (child-keys      [s] [(first remaining-keys)])
  (get-child       [s child-key]
    (assert (= child-key (first remaining-keys)))
    (let [inner-child (get-child wrapped-sp child-key)
          more-keys   (next remaining-keys)]
      (if more-keys
        (make-wrapped-subproblem inner-child more-keys output-set)
        (do (assert (state-set/subset? (:output-set inner-child) output-set))
            inner-child))))
  (refine-input    [s refined-input-set]
    ...?))

(defn make-wrapped-subproblem [wrapped-sp remaining-keys output-set]
  (WrappedSubproblem. (input-set wrapped-sp) wrapped-sp remaining-keys output-set))
















;; Refinements all have at least one action, constraints are new primitives.
;; TODO: need some superstructure to take into account initial 0-reward bound.

;; Some ideas to simplify for now:
;; - assume set of refinements fixed in advance, so we can use superstructure
;; - assume we always evaluate supers first
;; - switch back to refine model from evaluate model. (but must deal with propagation)


(comment
  ;; Again, sets but not costs
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

;; Super-structure always mirrors, when it exists?
;; But, sub-structure can get ahead, then things get out of whack. (lose track of it)
;; Suggests tighter integration, more structure sharing
;; But, as before, this is really difficult with current immediate-refinements-set
;; --> Should only allow dependence on req-known things, so can share upwards too.

;; Point two: when we go up, who are our supers?
;; Clearly, next of our super is one (as always)
;; Also, ultimate source of supers -- parent's next.
;; If we have both ???  Sure, can have full set of supers.
;; Pick them up as we go.  Still have *evaluation* problem, see above.

;; Before getting too detailed, how does this solve our cost problems?

;; Note we still end up with one OutputNode per (lowest-level) refinement,
;; So we get no compression so far.  But anyway, idea is that output tree
;; rooted at action output is all you need to know about it -- enough for transparency.

;; Now, suppose we propagate rewards backwards.
;; Each AIO assigned min-max reward to goal.
;; a.k.a min(parents, sups, next-step+immed, max(refs of next - step+o)
;; Close, but we lose comp --
;; also/instead want to propagate steps (instead?)

;; Steps go forward, up parent links, down sub links.  This still missing above-- no way to collect steps.
;; 

;; What if we replace ActionInstance with:
;; Map from InputSet to OutputRoot (or nil for uneval).


;; MAke a special finish that cannot be evaluated.
;; Now, can start with all unevaluated actions (ends of the line). Push reward back, up to parentAI, down to subs.
;; This leaves out pushing down refs.  Allows to "fill in" for unevaluated refs. That would be unnec. with superstructure?
;; Problem: how do we determine current best bound? 
;; Idea: costs go forward, down to refinements, only up when necessary. (i.e, unevaluated node).
;; Bound is only relevant if it includes at least one live thing???
;; But, we really want to do factored evaluation of costs.

;; Bound(AN) = min(Reward(AN), Bound(SupAN), max(Bound(RefinementNodes)))
;; Bound(RN) = min(PathSum(FirstAN))
;; PathSum(AN) = Bound(AN) + (no more ???)

;; Suppose we have OutputLattice on












(comment
;; Old versions -- work for set computation, but not costs.
  
(defrecord ActionInstance
  [parent-ri
   super-ai
   prev-aio
   actions ; this and following in refinement.
   output-atom ])

(defrecord ActionInstanceOutput
  [prev-ai
   output-set
   step-reward
   refinements
   next-ai-atom])

(def +worst-aio+ (ActionInstanceOutput. nil state-set/empty-lfss is/neg-inf nil nil))

(defrecord RefinementInstance
  [parent-ai
   super-ri
   first-ai-atom])

(defn make-refinement-instance [parent-ai actions]
  (let [ri (RefinementInstance. parent-ai nil (atom nil))]
    (reset! (:first-ai-atom ri)
            (ActionInstance. ri nil (:prev-aio parent-ai) actions (atom nil)))
    ri))


(defn make-refinement-instance-child [parent-ai sup-ri]
  (let [ri (RefinementInstance. parent-ai sup-ri (atom nil))
        sup-ai (-> sup-ri :first-ai-atom deref)]
    (reset! (:first-ai-atom ri)
            (ActionInstance. ri sup-ai (:prev-aio parent-ai) (:actions sup-ai) (atom nil)))
    ri))

(defn make-aio [ai]
  (let [{:keys [parent-ri super-ai prev-aio actions output-atom]} ai]
    (assert (nil? @output-atom))
    (let [input-set (:output-set prev-aio)
          [a & r]   actions
          prim?    (env/primitive? a)
          [opt rew] (angelic/optimistic-set-and-reward a input-set)]
      (if (or (not opt) (state-set/empty? opt) (= rew is/neg-inf))
        +worst-aio+
        (ActionInstanceOutput.
         ai opt rew
         (lazy-seq
          (let [super-refs (ccc/-?> super-ai :output-atom deref refinements)]
            (cond (and super-refs (not (= super-refs :blocked)))
                    (for [super-ri super-refs]
                      (make-refinement-instance-child ai super-ri))
                  (angelic/can-refine-from-set? a input-set)
                    (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
                      (make-refinement-instance
                       ai
                       (cons (env-util/make-factored-primitive [:noop] constraint {} 0) ref))
                  :else
                  :blocked))))
         (atom nil))))))

(defn extend-aio! [aio]
  (when-let [ai (:prev-ai aio)]
    (let [target-ai (util/find-first #(> (count (:actions %)) 1)
                                     (iterate #(-> % :parent-ri :parent-ai) ai))]
      (reset! (:next-ai-atom aio)
              (ActionInstance.
               (:parent-ri target-ai)
               (if (not (identical? ai target-ai))
                 target-ai
                 (ccc/-?> ai :super-ai output-atom deref next-ai-atom deref))
               aio
               (next (:actions target-ai))
               (atom nil))))))

(defn evaluate-ai! [ai]
  (let [aio (make-aio ai)]
    (reset! (:output-atom ai) aio)
    (extend-aio! aio)))
)