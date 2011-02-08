(ns angelic.search.implicit.dash-astar-opt
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.summary :as summary]            
            [angelic.search.summary-graphs :as sg]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

;; A relatively clean version of dash-A*, for optimistic descriptions only.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Options      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set! *warn-on-reflection* true)

;; These are all bound by the implicit-dash-a* main fn at the end of this file.
(declare *left-recursive*        ) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(declare *collect-equal-outputs* ) ;; Collect descendants with identical output sets
(declare *decompose-cache*       ) ;; Cache subproblems? Requires *collect-equal-outputs*
(declare *state-abstraction*     ) ;; Use state abstraction?  Requires *decompose-cache*
(declare *propagate-subsumption* ) ;; Automatically propagate subsumption links to corresponding children
(declare *dijkstra-actions*      ) ;; Use dijkstra for these action types (set).


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;         PubSubHub          ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord PubSubHub [^ArrayList subscribers ^ArrayList publications])

(defn- make-pubsubhub
  "A hub for publications streams; every subscriber fn is called on every publication."
  [] (PubSubHub. (ArrayList.) (ArrayList.)))

(defn- publications [psh] (doall (seq (:publications psh))))

(defn- publish!     [psh pub]
  (.add ^ArrayList (:publications psh) pub)
  (doseq [sub (doall (seq (:subscribers psh)))] (sub pub)))

(defn- subscribe!   [psh sub]
  (.add ^ArrayList (:subscribers psh) sub)
  (doseq [pub (doall (seq (:publications psh)))] (sub pub)))

;;;;;;;;;;;;;;;;;;;;;;;;;      Change Scheduling      ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Trying to keep cached summaries up-to-date while simultaneously modifying the
;; subproblem graph is quite difficult and potentially error-prone.
;; This code allows the set of root subproblems with changed summaries to be recorded
;; during evaluation and tree update, and then played back once the tree is fixed,
;; decoupling the processes of tree change and summary updates.

(def *increases* (ArrayList.))
(def *decreases* (ArrayList.))
(def *subsumes* (ArrayList.))

(defn- schedule-increase! [sp] (.add ^ArrayList *increases* sp))
(defn- schedule-decrease! [sp] (.add ^ArrayList *decreases* sp))
(defn- schedule-subsumption! [ts subsumed-ts] (.add ^ArrayList *subsumes* [ts subsumed-ts]))

(defn- do-changes! [^ArrayList a f] (doseq [sp a] (f sp)) (.clear a))

(declare evaluate!)

(defn- evaluate-and-update! [s]
  (evaluate! s)
  (do-changes! *increases* sg/summary-increased!) 
  (do-changes! *subsumes* (fn [[ts subsumed-ts]] (sg/connect-subsumed! ts subsumed-ts)))
  (do-changes! *decreases* sg/summary-changed!))

;;;;;;;;;;;;;;;;;;;;;;;;;;      Tree Summarizers      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol TreeSummarizer
  "A 'semantic' summarizer for a subproblem.  Its summarizer represents the best-
   known Summary for a subproblem and all its descendants"
  (ts-sp [ts] "The canonical subproblem summarized by this tree summarizer."))

(defn- make-tree-summarizer [sp]
  (let [ret (traits/reify-traits [sg/or-summarizable sg/simple-cached-node]
              TreeSummarizer (ts-sp [ts] sp))]
    (sg/connect! ret sp)
    (schedule-subsumption! ret sp)
    ret))

(defmethod print-method angelic.search.implicit.dash_astar_opt.TreeSummarizer [s o]
  (print-method (format "#<TS %s>" (print-str (ts-sp s))) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Protocol  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subproblem must also implement Summarizable; should take bound into account.
(defprotocol Subproblem
  (sp-name             [s] "A name to identify this subproblem type (indep. of input)")
  (input-set           [s] "Input set for this subproblem.")
  (sp-ts               [s] "Summarizer that includes outputs/children.")
  (evaluate!           [s] "Evaluate or throw exception if not evaluable.")

  (get-output-set      [s]   "Return output pair or nil")
  (add-output-watcher! [s w] "Add watcher to be notified of self when has output.")
  (set-output-set!     [s o] "Set output set.")

  (get-children        [s]       "List current children, for debugging only.")
  (add-child-watcher!  [s w]     "Add a watcher to be notified of published child subproblems.")
  (add-sp-child!       [s o up?] "Add a new subproblem child, published when ready.")

  (add-all-child-watcher! [s w] "Internal.  Watch children, including unpublished ones.")
  (subsuming-sps       [s]      "Known subproblems with same name, >= inp-set") 
  (add-subsuming-sp!   [s subsuming-sp] "Add subsuming sp") 

  (refine-input        [s refined-input-set] "Return a sp with same name, given subset of input-set. s must have output."))

(defmethod print-method angelic.search.implicit.dash_astar_opt.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s %s>" (System/identityHashCode sp) (sp-name sp)
                        (if (get-output-set sp) :OUT :STUB)) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Auxillary fns  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(defn- get-output-set! [sp] (let [o (get-output-set sp)] (assert o) o))

(defn- terminal? [sp]
  (and (empty? (get-children sp))
       (not (summary/live? (sg/summary sp)))))

(defn- solved-terminal? [sp]
  (and (empty? (get-children sp))
       (summary/solved? (sg/summary sp))))

;; Canonical SPs are Atomic and Pair; wrappers use TS of inner SP.
(defn- canonicalize [sp] (ts-sp (sp-ts sp)))

(defn- canonical? [sp] (identical? sp (canonicalize sp)))

(defn- connect-and-watch! [p c out-f child-f]
  (sg/connect! p c)
  (when out-f (add-output-watcher! c out-f))
  (add-child-watcher! c child-f))

(defn- connect-and-watch-ts! [p c out-f]
  (sg/connect! p (sp-ts c))
  (add-output-watcher! c out-f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Constructors  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- make-subproblem
  "Make a subproblem with the given name and input-set.  If this is a wrapping
   subproblem (e.g., output collector or state abstractor), pass tree summarizer
   of wrapped SP; otherwise, pass nil and a tree summarizer will be created.
   eval!-fn, ri-fn, and summary-fn specify how to evaluate, refine input, and summarize."
  [nm inp-set wrapped-ts eval!-fn ri-fn summary-fn]
 (let [                 ts-atom          (atom wrapped-ts)
       ^PubSubHub       output-ps        (make-pubsubhub)
       ^PubSubHub       child-ps         (make-pubsubhub)
       ^PubSubHub       all-child-ps     (make-pubsubhub) ;; For sub-following -- remove if no help.
       ^IdentityHashMap subsuming-sp-set (IdentityHashMap.)]
  (traits/reify-traits [sg/simple-cached-node]
   sg/Summarizable (summarize [s] (summary-fn s))
   Subproblem
  (sp-name             [s] nm)
  (input-set           [s] inp-set)
  (sp-ts               [s] (or @ts-atom (reset! ts-atom (make-tree-summarizer s))))
  (evaluate!           [s] (eval!-fn s))
  
  (get-output-set      [s] (first (publications output-ps)))
  (add-output-watcher! [s w] (subscribe! output-ps w))
  (set-output-set!    [s o] (assert (not (get-output-set s))) (publish! output-ps o))
  
  (get-children        [s] (publications child-ps))
  (add-child-watcher!  [s w] (subscribe! child-ps w))
  (add-sp-child!       [sp child-sp up?] ;; TODO: subsumption should prevent child from getting output before parent ??
   (util/print-debug 2 "AC" sp child-sp)
   (assert (get-output-set sp))
   (when (canonical? sp)
     (schedule-subsumption! (sp-ts sp) (sp-ts child-sp))
     (publish! all-child-ps child-sp))
   (let [pub! (fn publish-sp-child! []
                (util/assert-is (not (identical? sp child-sp)))
                (util/assert-is (and (get-output-set sp) (get-output-set child-sp)))
                (when (canonical? sp)
                  (sg/connect! (sp-ts sp) (sp-ts child-sp))
                  (schedule-increase! (sp-ts sp)))    
                (publish! child-ps child-sp))]
     (if (get-output-set child-sp)
       (pub!)
       (do (sg/connect! sp (sp-ts child-sp)) 
           (add-output-watcher! child-sp
              (fn [_] (pub!) 
                      (sg/disconnect! sp (sp-ts child-sp))
                      (schedule-decrease! sp)))
           (when up? (schedule-increase! sp))))))

  (add-all-child-watcher! [s w] (subscribe! all-child-ps w))    
  (subsuming-sps [s] (keys subsuming-sp-set))
  (add-subsuming-sp! [s subsuming-sp]
    (util/assert-is (canonical? s))
    (util/assert-is (canonical? subsuming-sp))                     
    (util/assert-is (= nm (sp-name subsuming-sp)))
    (when-not (or (identical? s subsuming-sp)
                  (.containsKey subsuming-sp-set subsuming-sp))
      (.put subsuming-sp-set subsuming-sp true)
      (schedule-subsumption! (sp-ts subsuming-sp) (sp-ts s))
      (when *propagate-subsumption*  ;; TODO: efficiency, etc.
        (add-all-child-watcher! s
          (fn [child]
            (let [can-child (canonicalize child)]
              (add-all-child-watcher! subsuming-sp
                (fn [subsuming-child]
                  (let [can-subsuming-child (canonicalize subsuming-child)]
                    (when (= (sp-name can-child) (sp-name can-subsuming-child))
                      (add-subsuming-sp! can-child can-subsuming-child)))))))))))
  
  (refine-input    [s ni]
    (let [ret (ri-fn s ni)]
      (util/assert-is (= nm (sp-name ret)))
      (when (canonical? s) (add-subsuming-sp! ret s))
      ret)))))

;; Multimethod to get a subproblem by name.
(defmulti get-subproblem (fn get-subproblem-dispatch [nm inp] (first nm)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Atomic subproblems represent the plans for a single action from an input set.

;; Initially, we are live with no children and 0 reward (or best subsuming bound).
;; On first evaluation, we compute and publish the output set, and adjust the reward.
;; If live, we can evaluate a second time, when we generate the child subproblems.
;; If we have a nonterminal subsuming subproblem, we generate by refining input of its children
;; Otherwise, we generate children from scratch using get-subproblem and refinement-names.

(defn atomic-name [fs] [:Atomic fs])

(defn make-summary [rew stat src]
  (let [b (sg/get-bound src)]
    (summary/make-simple-summary (if rew (min rew b) b) stat src)))

(declare refinement-names)

;; TODO: subsuming sp can become blocked before its children come to fruition...
;; TODO: fix in dash_astar too.
;; Easiest solution: pair not blocked until it has output.
(defn- make-atomic-subproblem [fs inp-set]
  (let [nm         (atomic-name fs)
        summary-fn (atom #(make-summary nil :live %))
        set-sf!    (fn [s f] (reset! summary-fn f) (schedule-decrease! s))] 
    (make-subproblem
     nm inp-set nil
     (fn evaluate! [s]
       (util/print-debug 1 "eval" nm (if (get-output-set s) :out :no-out))
       (if-not (get-output-set s) ; Not evaluated yet -- evalute description and publish output
         (let [[out-set reward status] (fs/apply-opt fs inp-set)]
	   (when-not out-set (util/assert-is (= reward Double/NEGATIVE_INFINITY)
					     "Bad outcome: %s" [(fs/fs-name fs) reward status]))
           (set-sf! s #(make-summary reward status %))
           (when out-set (set-output-set! s out-set)))
         (do (set-sf! s sg/or-summary) ; Evaluated to live -- generate children now.
             (if-let [subsuming-sps (seq (filter #(not (terminal? %)) (subsuming-sps s)))]
               (connect-and-watch! s (apply min-key (comp sg/get-bound sp-ts) subsuming-sps) nil
                 (fn [sub-out] (add-sp-child! s (refine-input sub-out inp-set) true))) 
               (doseq [ref-name (refinement-names fs inp-set)] ;		 (println fs ref-name)
                 (add-sp-child! s (get-subproblem ref-name inp-set) false))))))     
     (fn [s ri]  (assert (not *collect-equal-outputs*))  
       (if (= ri inp-set) s (get-subproblem nm  ri)))
     (fn summarize [s] (@summary-fn s)))))

(defmethod get-subproblem :Atomic [[_ fs :as n] inp-set] 
  (make-atomic-subproblem fs inp-set))          



;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Dijkstra       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This subproblem does a flattened, pruned search for right-recursive HLAs.

;; TODO: how do i know if i'm already in a dijkstra or not?
;; Does it matter?
;; If we have dijkstra all the way down, don't even need full dijkstra?
;; Nah, remember whole deal about GG versus Dijkstra versus Caching.
;; Dijkstra all the way down means n dijkstras running, no fun.
;; For now, just do straight top-level dijkstra, skip caching of right.
;; I.e., generate our own refinements.  Just use pairs, doens't matter since
;; everything will be solved already.
;; Directly implements evaluable, so we don't need to show our queue to the outside
;; world; and we can eagerly evaluate left children.

(use '[edu.berkeley.ai.util.queues :as queues])

(declare wrapped-atomic-name)

(defn dijkstra-name [fs] [:Dijkstra fs])

;; This seems a bit dangerous, but should be ok...
(defn get-evaluated-sp [fs inp-set]
  (let [n (wrapped-atomic-name fs)
        s (get-subproblem n inp-set)]
    (when (summary/live? (sg/summary s))
      (evaluate! (ts-sp (sp-ts s)))
      (sg/summary-changed! (ts-sp (sp-ts s))))
    (assert (summary/solved? (sg/summary s)))
    s))


;; We bend the rules a bit and eval immediately, for simplicity.
(defn make-dijkstra-subproblem [fs inp-set]
  (let [nm (dijkstra-name fs)
        q  (queues/make-graph-search-pq)
        ret (make-subproblem
             nm inp-set nil
             (fn eval-dijkstra! [s]
;               (println "EVAL" s)
               (assert (not (queues/pq-empty? q)))
               (schedule-decrease! s)
               (let [[mid-set [_ _ _ _ prim-r]] (queues/pq-remove-min-with-cost! q)]
                 (doseq [child-seq (fs/child-seqs fs mid-set)]
                   (assert (#{1 2} (count child-seq)))
                   (when (= 2 (count child-seq)) (assert (= (second child-seq) fs)))
                   (let [l (get-evaluated-sp (first child-seq) mid-set)
                         next-mid-set (get-output-set! l)
                         next-prim-r (+ prim-r (summary/max-reward (sg/summary l)))]
;                     (when (= 1 (count child-seq)) (println l (sg/summary l)))
                     (if (= 1 (count child-seq))
                       (queues/pq-replace! q next-mid-set [(- 0 next-prim-r) -2 next-prim-r :solved :d])
                       (let [[out-set reward status] (fs/apply-opt fs next-mid-set)]
                         (when out-set
                           (let [tot-rew (+ next-prim-r reward)]
                             (queues/pq-add! q next-mid-set
                                             [(- 0 tot-rew) (- (summary/status-val status))
                                              tot-rew status next-prim-r])))))))))             
             (fn [s ri] (make-dijkstra-subproblem fs ri))
             (fn summarize [s]
;               (println "SUM" s (que))
               (if (queues/pq-empty? q)
                 (make-summary Double/NEGATIVE_INFINITY :blocked s)
                 (let [[_ [_ _ reward status]] (queues/pq-peek-min q)]
                   (make-summary reward status s)))))]    
    (let [[out-set reward status] (fs/apply-opt fs inp-set)]
      (set-output-set! ret out-set)
      (queues/pq-add! q inp-set [(- reward) (- (summary/status-val status)) reward status 0]))
    ret))


(defmethod get-subproblem :Dijkstra [[_ fs :as n] inp-set] 
  (make-dijkstra-subproblem fs inp-set))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Pair      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pair subproblems represent sequntial composition of two subproblems.

;; Thus, we use the output of the left-sp as input for right-sp,
;; and output of right-sp as output of the pair.

;; The slightly tricky part is generating children.  Both left-sp and right-sp
;; may have childen, but to search systematically we should branch on only one at a time.
;; This means that our summary should consist of the sum of summaries of
;;   - The subproblem whose children we branch on, and
;;   - The tree summarizer of the other subproblem.

;; For now, always attempt to branch on the left subproblem first, unless the
;; left subproblem is terminal (no children), in which case we branch right.
;; Unfortunately, we don't know when we start if the left will be terminal
;; (under *collect-equal-outputs*), so we assume it's not, then switch if,
;; at any point, it becomes terminal.
;; Unfortunately, the only place we can tell if it becomes terminal is while
;; computing the summary of this node.  But, at that point we don't want to
;; trigger any tree modifications, since when summary updates and tree modifications
;; get interleaved arbitrarily, it gets really hard to maintain correctness.
;; So, if right-sp already has children, we make the SP a leaf and wait for
;; it to be evaluated to switch; otherwise, we safely switch immediately.

(defn pair-name [l r] [:Pair l r])

;; TODO: short circuit when left terminal? (can we know soon enough?)
;; TODO: no right output when right blocked?
;; TODO: new approach of not branching at all until fully evaluated
;;       is worse in terms of evals than old -- perhaps subsumption blocking would be better?

(defn- make-pair-subproblem
  ([left-sp right-sp] (make-pair-subproblem left-sp (sp-name right-sp) (constantly right-sp)))
  ([left-sp right-name right-sp-fn]
     (let [nm (pair-name (sp-name left-sp) right-name)
           right-sp (delay (right-sp-fn (get-output-set! left-sp)))
           right?-atom (atom false) ;; Expand on right            
           ss (sg/make-sum-summarizer)
           go-right! (fn [s] ;		       (println "GR" s)
                       (reset! right?-atom true)                          
                       (sg/disconnect! ss (sp-ts @right-sp))
                       (add-child-watcher! left-sp (fn [c] (def *bad* [s c]) (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch! ss @right-sp nil
                         (fn right-child [right-child] (add-sp-child! s (make-pair-subproblem left-sp right-child) true)))
                       (sg/summary-changed-local! ss))
           ret (make-subproblem nm (input-set left-sp) nil 
                 (fn eval! [s] (util/print-debug 1 "eval-pair" nm) (schedule-decrease! s) (go-right! s)) 
                 (fn [s ni] (if (= ni (input-set left-sp)) s
                                (make-pair-subproblem (refine-input left-sp ni)
                                                      right-name #(refine-input @right-sp %))))
                 (fn [s] 
                   (or (and (get-output-set s)
                            (not @right?-atom)
                            (solved-terminal? left-sp)
                            (if (empty? (get-children @right-sp))
                              (do (go-right! s) nil)
                              (let [r (min (summary/max-reward (sg/summary ss)) (sg/get-bound s))]
                                (make-summary r :live s)))) ;; tODO: ??
                       (sg/or-summary s))))]    
       (sg/connect! ret ss) 
       (connect-and-watch-ts! ss left-sp
         (fn left-output [_]
           (connect-and-watch-ts! ss @right-sp
           (fn right-output [o]
             (set-output-set! ret o)
             (sg/disconnect! ss (sp-ts left-sp))
             (connect-and-watch! ss left-sp nil
               (fn left-child [left-child]
                 (add-sp-child! ret (make-pair-subproblem left-child right-name #(refine-input @right-sp %)) true)))
             (schedule-decrease! ss)))           
           (schedule-decrease! ss))) 
       ret)))


(defmethod get-subproblem :Pair [[_ left-name right-name :as n] inp]
  (make-pair-subproblem (get-subproblem left-name inp) right-name #(get-subproblem right-name %)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-wrapped-subproblem
  "Make a wrapped subproblem, which modifies the behavior of a wrapped 'canonical'
   subproblem while retaining the same semantics, tree summarizer, etc."
  [nm inp-set prefix-set inner-sp output-wrap child-watch ri-fn]
  (util/assert-is (contains? prefix-set (first (sp-name inner-sp))))
  (let [ret (make-subproblem nm inp-set (sp-ts inner-sp)
                             (fn [_] (throw (RuntimeException.)))
                             ri-fn sg/or-summary)]
    (connect-and-watch! ret inner-sp
      (fn [o] (set-output-set! ret (output-wrap o)))
      (fn [inner-child] (child-watch ret inner-child)))
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Output Collector captures children with the same output set, and only
;; releases new children for refined output sets.

;; OutputCollector also handles decomposition and inside of state abstraction, when applicable.

(defn oc-name [inner-name] [:OC inner-name])



(defn atomic-name-fs [n] (assert (#{:Atomic :Dijkstra} (first n))) (second n))
(defn log-input [fs inp-set] (if *state-abstraction* (fs/get-logger fs inp-set) inp-set))
(defn get-input-key [fs inp-set] (if *state-abstraction* (fs/extract-context fs inp-set) inp-set))

(declare get-ocs)

;; Input-key caching not necessary, but speeds things up a lot on, e.g., discrete-manipulation.
;; TODO: only :Atomic or :Pair inside, when SA off 
(defn- make-output-collecting-subproblem [fs inp-key inner-sp]
  (make-wrapped-subproblem
   (oc-name (sp-name inner-sp)) (input-set inner-sp) #{:Atomic :Dijkstra :Pair #_ ::TODO??? :SA :OC} inner-sp
   identity
   (fn child-watch [sp child-sp] 
     (if (fs/=-state-sets (get-output-set! inner-sp) (get-output-set! child-sp))
       (do (schedule-increase! sp) (connect-and-watch! sp child-sp nil #(child-watch sp %))) 
       (add-sp-child! sp (make-output-collecting-subproblem fs inp-key child-sp) :irrelevant))) 
   (fn refine-input [s ni]
     (let [ninp-key (get-input-key fs ni)]
       (if (= inp-key ninp-key)
         s
         (if (#{:Atomic :Dijkstra} (first (sp-name inner-sp))) ;; TODO!
           (let [ret (get-ocs (sp-name inner-sp) fs ninp-key ni)]
             (util/assert-is (not (identical? (canonicalize ret) inner-sp)) "%s" [(def *bad* [s inner-sp (input-set s) ni])])
             (add-subsuming-sp! (canonicalize ret) inner-sp)
             ret)
           (make-output-collecting-subproblem fs ninp-key (refine-input inner-sp (log-input fs ni)))))))))

(defn get-ocs [inner-n fs inp-key inp-set] 
  (let [make-sp #(make-output-collecting-subproblem fs inp-key (get-subproblem inner-n (log-input fs inp-set)))]
    (if-let [^HashMap dc *decompose-cache*]
      (util/cache-with dc [inner-n inp-key] (make-sp))
      (make-sp))))

(defmethod get-subproblem :OC [[_ inner-n :as n] inp-set]
  (let [fs (atomic-name-fs inner-n)] (get-ocs inner-n fs (get-input-key fs inp-set) inp-set)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;     State Abstraction     ;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State abstractor puts the output of a subproblem (and all children) in a new context.

(defn sa-name [inner-name] [:SA inner-name])

;; Note: subsumed subproblems can have different irrelevant vars
;; Also note: new input can have subset of variables of old. (=-state-sets does ntthis now).
(defn- make-state-abstracted-subproblem [fs inner-sp inp-set]
  (make-wrapped-subproblem
   (sa-name (sp-name inner-sp)) inp-set #{:OC} inner-sp
   (fn [o] (fs/transfer-effects inp-set o))
   (fn [sp child-sp] (add-sp-child! sp (make-state-abstracted-subproblem fs child-sp inp-set) :irrelevant)) 
   (fn [sp ni] #_ (def *bad* sp) (if (fs/=-state-sets ni inp-set) sp (make-state-abstracted-subproblem fs (refine-input inner-sp ni) ni)))))

(defmethod get-subproblem :SA [[_ inner-n :as n] inp-set]
  (let [fs (atomic-name-fs (second inner-n))] 
    (make-state-abstracted-subproblem fs (get-subproblem inner-n inp-set) inp-set)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Refinement Names     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- left-factor [is]
  (loop [s (next is) ret (first is)]
    (if s (recur (next s) (pair-name ret (first s))) ret)))

(defn- right-factor [[f & r]]
  (if (seq r) (pair-name f (right-factor r)) f))

(defn- wrapped-atomic-name [fs]
  (let [in  (if (*dijkstra-actions* (first (fs/fs-name fs)))
              (dijkstra-name fs)
              (atomic-name fs))
        mid (if *collect-equal-outputs* (oc-name in) in)]
    (if *state-abstraction* (sa-name mid) mid)))


(defn- refinement-names
  "Generate the names of subproblems representing refinements of fs from inp-set"
  [fs inp-set]
  (for [fs-seq (fs/child-seqs fs inp-set)]
    ((if *left-recursive* left-factor right-factor)
     (map wrapped-atomic-name fs-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)

(defn wtd-sample [item-wt-pairs]
  (let [tot-wt (reduce + (map second item-wt-pairs))]
    (loop [[[item wt] & more-items] (seq item-wt-pairs)]
      (cond (empty? more-items) item
            (<= (rand) (/ wt tot-wt)) item
            :else (recur more-items)))))

;; Doesn't really do what's intended, since solved wt is counted too.
(defn even-sample [nodes]
  (wtd-sample (for [n nodes] [n (inc (- (summary/max-reward (sg/summary n))))])))


(defn implicit-dash-a*-opt
  "Solve this hierarchical env using implicit DASH-A*, or variants thereupon.  Options are:
    :gather    Don't publish child subproblems with identical outputs?
    :d         Decomposition: cache and re-use subproblems by [name inp-set] pair?  Requires :gather.
    :s         State Abstraction: take state abstraction into account when caching?  Requires :d.
    :choice-fn Choose a child node to evaluate from alternatives (in sequence)
    :local?    Apply choice-fn recursively at each pair, or to an entire leaf sequence (slower)?
    :dir       Factor sequences into pairs using :left or :right recursion
    :prop      Automatically propagate subsumption from parents to matching children?"
  [henv & {gather :gather d :d  s :s   choice-fn :choice-fn
           local? :local?  dir :dir   prop :prop dijkstra :dijkstra :as m
      :or {gather true   d true s true choice-fn last
           local? true     dir :right prop true dijkstra #{}}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir :prop :dijkstra} (keys m)))
  (when s (assert d))
  (when d (assert gather))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (case dir :left true :right false)
            *propagate-subsumption* prop
            *dijkstra-actions*      dijkstra]
    (def *root* (sp-ts (apply make-atomic-subproblem (reverse (fs/make-init-pair henv)))))
    (summary/solve
     #(sg/summary *root*)
     (sg/best-leaf-operator choice-fn local? evaluate-and-update!)
     #(let [fs (second (sp-name %)) n (fs/fs-name fs)] (when-not (= (first n) :noop) fs)))))



;; (do (use 'edu.berkeley.ai.util '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.domains.discrete-manipulation 'angelic.search.implicit.dash-astar-opt) (require '[angelic.search.summary-graphs :as sg] '[angelic.search.summary :as summary]) (defn s [x]  (sg/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (sg/child-nodes x)))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 4 0) true)]  (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))






