(ns angelic.search.implicit.dash-astar
  (:require [angelic.util :as util]
            [angelic.util.traits :as traits]
            [angelic.search.summary :as summary]            
            [angelic.search.summary-graphs :as sg]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

;; An extensions of dash_astar_opt to include pessimistic trees.

;; Here we replace all subsumption with consistency-maintaining and TDBs in summaries.
;; This simplifies problems with cycles that arrise when doing subsumption right.
;; Note: with good descriptions, subsumption/TDB has two purposes?
;;  1.  Give subproblems a bound before they have output.
;;  2.  Account for necessary inconsistency with implicit descriptions.

;; Note: assume optimistic description is exact when solved-terminal, share with pess
;; (only when output-collecting on...)

;; TODO: tests ! 

;;;;; Subsumption
;; TODO: Figure out why propagation isn't more helpful.
;; TODO: propagate to halves of pairs ?
;; TODO: more generic propagation?  (We know: names, subs. relationships on sets.  Efficient lookups?)
;; TODO: children wait on one (or more) subsumption parents.

;;;;; Pessimistic
;; TODO: hook up pess/opt with same input set?
;; TODO: pruning. ?
;; --> TODO: empty-set subproblems for pessimistic.
;; --> TODO: Cannot propagate upper bounds from pessimistic subproblems
;;           in the presence of sharing, since they may reflect other opt SPs.
;; TODO: set max-gap to something reasonable for -inf pess bounds.
;; TODO: commitment, i.e., pruning from pess tree ? 

;;;;; Tree construction
;; -> TODO: dijkstra variants for cyclic actions ??
;; TODO: smarter output-collector (semantic) -- problems here though.
;; TODO: don't always split-left?
;; TODO: don't release children until they have lower reward or are primitive? 
;;--> TODO: alternative child release strategies, e.g. wait 'til solved
;; TODO: make sure dead stuff can be GC'd
;; TODO: note no difference between syntax and semantics for single state ...
;; TODO: use sharing for solved-terminal? problems everywhere (e.g. ,when SA off)
;;    (even when SA on -- primitics can funnel)

;;;;; Summaries and solving 
;; TODO: lazy/pseudo-solve (regular seems impossible; bounds mean apparent decrease may be increase.
;;    I.e., live decrease -50 to -49, now blocked sibling becomes best; above is -50 TDB;
;; TODO: smarter summary updates (i.e., pass child)
;; TODO: smarter choose-leaf?
;; TODO: conspiracy number, weighted, etc.
;; TODO: forcing summary of TS in summary_graphs makes a lot of extra comps (lefts), doesn't help.
;; TODO: propagate across subsumption links? (must be careful here, not to cross state/plan syntax/semantics line)

;;;;; SP caching
;; TODO: tail (i.e., pair) caching? -- Only help for >2 len refs...
;; TODO: cache refine-inputs?
;; TODO: cache children of output-collector? ~15 examples >1 in dm 4-3...
;; TODO: investigate plan seq  normalization. (flattening)

;;;;; Weighted
;; TODO: make sure incorrect weights from bounding are OK.
;; TODO: smarter choices (max of alpha * max-rew?)
;; TODO: figure out why weighted is worse, even with weight=1.
;; -->  Problem 1: totally unevaluated things don't pay proper weight?  (try immediate eval?!)
;; --> Problem 2: weights aren't propagated by subsumption.  Refine-input leads to huge jump.
;; --> Problem 3: solved has weight != f. (always take solved if within weight???)
;; TODO: increase should be talking about *bound* or *status* increase ?? (not general >= )
;; --> First things:
;;    --> atomic without output should use complete summary of subsuming (incl. wtd)
;;    --> pair without right should use sum of left and complete summary of subsuming right

;; Basic idea behind "wait on subsumption":
;;   Don't do anything with child of node with subs. parent
;;   until child has at least one subs. parent (or subs. parents are done.)
;; Can be implemented by not letting children go until they have subs...
;;  (and not incorporating into summary, except as bound) .... ?

;; Current pess thing is broken -- should go other way!
;;  (gathering happens on opt side!).
;; Then, two questions:
;;   - How does propagation work?
;;     - Lower bounds should be propagated *up* subsumption links?
;;   - How does pess side get evaluated?
;;     - After eval opt, eval pess if needed?

;; TODO: watch out for increases that were previously decreases...

;; What can happen without subsumption bounding:
;; left of pair is evaluated, right is still a stub.
;; left spits out a child.  we try to refine-input of right.
;;  two bad consequences: (1) may never provide output for SP
;;                        (2) can try to refine-input of right without output
;;                           (b) this can lead to refine-input of non-existent right within rught stub child.
;; Potential solutions: subsumption bounding, or just fix pair -- no branching until done. 


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
(def *eager-evaluation*  false   ) ;; Evaluate descriptions of new atomic subproblems immediately.

(declare *make-opt-summary*      ) ;; fn of [min-reward status source]
(declare *make-opt-or*           ) ;; fn of [sp-name]
(declare *make-pess-summary*     ) ;; fn of [min-reward max-reward status source children]
(declare *make-pess-or*          ) ;; fn of [min-reward max-reward status source children]

(def *share-terminal* true       )

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

(defprotocol Evaluable
  (evaluate! [s])
  (sp-name             [s] "A name to identify this subproblem type (indep. of input)"))

(defn- evaluate-and-update! [s]
  (evaluate! s)
  (do-changes! *increases* sg/summary-increased!)
  (do-changes! *subsumes* (fn [[ts subsumed-ts]] (sg/connect-subsumed! ts subsumed-ts)))
  (do-changes! *decreases* sg/summary-changed!))

;;;;;;;;;;;;;;;;;;;;;;      Summaries and Summarizers      ;;;;;;;;;;;;;;;;;;;;;

(defn make-summary [type rew stat src bound]
  (let [b (min bound (sg/get-bound src))]
    (case type
      :opt  (*make-opt-summary*  (if rew (min rew b) b) stat src)
      :pess (*make-pess-summary* (or rew summary/neg-inf) b stat src nil))))

(defn make-or-summarizer [type sp-name init-bound]
  (case type
    :opt  (*make-opt-or* sp-name)
    :pess (*make-pess-or* sp-name init-bound)))

#_(sg/make-sws-or-summary init-bound  #(or (tree-summarizer? %) (empty? (get-children %))))



;;;;;;;;;;;;;;;;;;;;;;;;;;      Tree Summarizers      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare input-set)

(defprotocol TreeSummarizer
  "A 'semantic' summarizer for a subproblem.  Its summarizer represents the best-
   known Summary for a subproblem and all its descendants"
  (ts-sp [ts] "The canonical subproblem summarized by this tree summarizer."))

(defn- make-tree-summarizer [sp]
  (let [os  (make-or-summarizer (first (input-set sp)) (sp-name sp) nil)
        ret (traits/reify-traits [sg/simple-cached-node]
              sg/Summarizable (summarize [ts] (os ts))
              TreeSummarizer  (ts-sp [ts] sp))]
    (sg/connect! ret sp)
    (schedule-subsumption! #_ sg/connect-subsumed! ret sp) ;; TODO: schedule, not connect???
    ret))

(defn tree-summarizer? [s] (instance? angelic.search.implicit.dash_astar.TreeSummarizer s))

(defmethod print-method angelic.search.implicit.dash_astar.TreeSummarizer [s o]
  (print-method (format "#<TS %s>" (print-str (ts-sp s))) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Protocol  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subproblem must also implement Summarizable; should take bound into account.
(defprotocol Subproblem
  (input-set           [s] "A pair [:opt/:pess state-set]")
  (sp-ts               [s] "Summarizer that includes outputs/children.")

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

(defmethod print-method angelic.search.implicit.dash_astar.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s %s %s>" (System/identityHashCode sp) (sp-name sp)
                        (first (input-set sp)) (if (get-output-set sp) :OUT :STUB)) o))

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

;; TODO: cleanup
(defn- connect-and-watch-subsuming! [sp subsuming-sp child-f]
  (sg/connect! sp
    (if (and (= (first (input-set sp)) :pess) (= (first (input-set subsuming-sp)) :opt))
      (sg/make-wrapping-summarizer subsuming-sp
        #(*make-pess-summary* summary/neg-inf (summary/max-reward %2) (summary/status %2) %1 [%2]))
      subsuming-sp))
  (add-child-watcher! subsuming-sp child-f))

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
   Evaluable
  (evaluate!           [s] (eval!-fn s))
  (sp-name             [s] nm)
   Subproblem
  (input-set           [s] inp-set)
  (sp-ts               [s] (or @ts-atom (reset! ts-atom (make-tree-summarizer s))))
  
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


;; Pair, SA, etc. has to be able to deal with no pess set...
;; For now, it should just not instantiate right?
;; Or, we can use special "bottom" set, instantiate dummy SP, etc.

;; Also, right now we can transition pess->opt by having opt as child when generating child.
;; We have to wrap this summary somehow ...

;; Wrapping/deferring should work as:
;;  If your parent has a nonterminal subsuming SP,
;;  and you have no subsuming SP,
;;  then your summary should be *min* of self & parent-subsuming (SP, not TS).
;;    (more precisely, parent-subsuming, bounded by self)
;;  This means we can cross-over, but summary type is preserved.

;; Is below still needed, or is this a special case ?

;; How can child end up without subsuming anyway?

;; How do we keep connection, e.g., when both opt and pess have refine-input ?

;; TODO: consistency of some sort for pess -- at least going up.
;;  (otherwise we lose it every time we eval)
;; TODO: think about ordering of pess, etc.
;;  (blocked with bound, etc. ) -- what are we trying to do ??
;; good question :/.  Spse we shoot for wtd. thing.

;; From explicit-dash-a*:
; This is the most straightforward application of wA* to the version of dash-A* in
; hierarchical-incremental-search.  We replace max-reward with max(opt * (1 + alpha * a_w), pess),
; where a_w is an optional action weight between 0 and 1.  We do not attempt to compute
; the true f-values.  This means no hard commitments, no adaptive weights. 

;; Current problems:
;;   max-reward of sws is not a real max-reward, bound screws us up 
;;   bounding of sws does not adjust f-val
;;   no min-bounding of sws.
;; Solution: somehow repurpose the bound for pess?
;;  i.e., bound with a summary instead of a number?
;;  or something ...
;;  can't really bound anything with SWS.
;;  Would still like to keep best opt bound, just don't pull from summary.
;;  Similarly, would like 

(declare refinement-names)

;; TODO TODO: subsuming SP can become blocked before it has children...
(defn- make-atomic-subproblem [fs inp-set]
  (let [nm         (atomic-name fs)
        summary-fn (atom #_ #(make-summary (first inp-set) nil :live % 0) 
                         (fn [s] (if-let [sub (first (subsuming-sps s))] ;; TODO: ???
                                   (summary/leafen (sg/summary (sp-ts sub))  (sg/get-bound s) :live s)
                                   (make-summary (first inp-set) nil :live s  (sg/get-bound s)))))        
        set-sf!    (fn [s f] (reset! summary-fn f) (schedule-decrease! s))]
   (doto 
    (make-subproblem
     nm inp-set nil
     (fn evaluate! [s]
       (util/print-debug 1 "eval" nm (if (get-output-set s) :out :no-out) (sg/summary s))
       (if-not (get-output-set s)
         ;; Not evaluated yet -- evalute description and publish output
         (let [[out-set reward status] ((case (first inp-set) :opt fs/apply-opt :pess fs/apply-pess) fs (second inp-set))]
           (set-sf! s (let [sub (and (= status :live) (first (subsuming-sps s)))] ;; TODO
                        (if (and sub (< (summary/max-reward (sg/summary sub)) 0))
                         #(summary/leafen (sg/summary (sp-ts sub)) (min reward (sg/get-bound s)) :live %)                        
                         #(make-summary (first inp-set) reward status % (sg/get-bound s)))))
           (when out-set (set-output-set! s [(first inp-set) out-set])))
         ;; Evaluated to live -- generate children now.
         (do (set-sf! s (make-or-summarizer (first inp-set) nm (:p-val (sg/summary s))))             
             (if-let [subsuming-sps (seq (filter #(not (terminal? %)) (subsuming-sps s)))]
               (connect-and-watch-subsuming! s (apply min-key (comp sg/get-bound sp-ts) subsuming-sps) ;; TODO: bound may not exist!
                 (fn [sub-out] (add-sp-child! s (refine-input sub-out inp-set) true))) 
               (doseq [ref-name (refinement-names fs inp-set)] #_ (println fs ref-name)
                 (add-sp-child! s (get-subproblem ref-name inp-set) false))))))     
     (fn [s ri]  (assert (or (not *collect-equal-outputs*) (and (= :pess (first ri)) (= :opt (first inp-set)))))  
       (if (= ri inp-set) s (get-subproblem nm  ri)))
     (fn summarize [s] (@summary-fn s)))
    (->> evaluate! (or (not *eager-evaluation*))))))


(defmethod get-subproblem :Atomic [[_ fs :as n] inp-set] 
  (make-atomic-subproblem fs inp-set))          

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

;; TODO TODO: avoid children-before-output set, like in dash_astar_opt or using
;; subsumption blocking.
;; TODO: short circuit when left terminal? (can we know soon enough?)
;; TODO: no right output when right blocked? 
(defn- make-pair-subproblem
  ([left-sp right-sp] (make-pair-subproblem left-sp (sp-name right-sp) (constantly right-sp) nil))
  ([left-sp right-name right-sp-fn right-sub-sp]
     (let [nm (pair-name (sp-name left-sp) right-name)
           right-sp (delay (right-sp-fn (get-output-set! left-sp)))
           right?-atom (atom false) ;; Expand on right            
           rz  (when (= :pess (first (input-set left-sp))) ; Right zero (pess needs neg-inf lower bound)
                 (traits/reify-traits [sg/summary-cache] sg/Summarizable
                  (summarize [s] (*make-pess-summary* summary/neg-inf 0 :solved s nil))))
           os  (make-or-summarizer (first (input-set left-sp)) nm nil)
           ret (make-subproblem nm (input-set left-sp) nil (fn [_] (throw (RuntimeException.))) 
                 (fn [s ni] (if (= ni (input-set left-sp)) s
                                (make-pair-subproblem (refine-input left-sp ni)
                                                      right-name #(refine-input @right-sp %) @right-sp)))
                 os)
           go-right! (fn [ss] 
                       (reset! right?-atom true)                          
                       (sg/disconnect! ss (sp-ts @right-sp))
                       (add-child-watcher! left-sp (fn [c] (def *bad* [ret c]) (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch! ss @right-sp nil
                         (fn right-child [right-child] (add-sp-child! ret (make-pair-subproblem left-sp right-child) true))))
           sum-summary (fn [s] ;; TODO: ???
                         (swap! sg/*summary-count* inc)
                         (let [kids (sg/child-nodes s)]
                           (assert (<= 1 (count kids) 2))                           
                           (cond (= (count kids) 2) (summary/+ (sg/summary (first kids)) (sg/summary (second kids)) s (sg/get-bound s))
                                 right-sub-sp       (summary/+ (sg/summary left-sp)
                                                               (sg/summary (sg/make-wrapping-summarizer (sp-ts right-sub-sp) (fn [dummy sub-sum] (summary/leafen sub-sum 0 :blocked dummy)))) s (sg/get-bound s))
                                 :else              (summary/re-source (sg/summary left-sp) s (sg/get-bound s) :solved))))           
           ss (traits/reify-traits [sg/simple-cached-node] ;; needed for wA*, at least ? 
                Evaluable
                (evaluate! [s] (util/print-debug 1 "Eval sum" nm (sg/sum-summary s)) (schedule-decrease! s) (go-right! s)  #_ (do (def *root2* *root*) (def *root* nil) (def *s* ret)))
                (sp-name [s] (conj nm :SS)) ;; Needed for wtd.
                sg/Summarizable
                (summarize [s]
                 (let [summ (sum-summary s)]
                   (if (and (not @right?-atom)
                           (solved-terminal? left-sp))
                     (if (empty? (get-children @right-sp))
                       (do (go-right! s) (sum-summary s))
                       (summary/leafen summ 0 :live s))
                    summ))))]    
       (sg/connect! ret ss)
;       (schedule-subsumption! ret ss) ;; TODO: remove ?  Here for bounding of pairs with SWS...
       (when rz (sg/add-child! ss rz))
       (connect-and-watch-ts! ss left-sp
         (fn left-output [_]
           (when rz (sg/remove-child! ss rz))
           (connect-and-watch-ts! ss @right-sp
             (fn right-output [o]
               (set-output-set! ret o)
               (sg/disconnect! ss (sp-ts left-sp))
               (connect-and-watch! ss left-sp nil
                 (fn left-child [left-child]
                   (add-sp-child! ret (make-pair-subproblem left-child right-name #(refine-input @right-sp %) @right-sp) true)))
               (schedule-decrease! ss)))           
           (schedule-decrease! ss)))
       ret)))

(comment ;; Old version -- better perf, but can fail -- see above.
  (connect-and-watch! ss left-sp
         (fn left-output [_]
           (when rz (sg/remove-child! ss rz))
           (connect-and-watch-ts! ss @right-sp (fn [o] (set-output-set! ret o)))
           (schedule-decrease! ss))
         (fn left-child [left-child]
           (add-sp-child! ret (make-pair-subproblem left-child right-name #(refine-input @right-sp %) @right-sp) true)))
  )



(defmethod get-subproblem :Pair [[_ left-name right-name :as n] inp]
  (make-pair-subproblem (get-subproblem left-name inp) right-name #(get-subproblem right-name %) nil))


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
                             ri-fn (make-or-summarizer (first inp-set) nm nil))]
    (connect-and-watch! ret inner-sp
      (fn [o] (set-output-set! ret (output-wrap o)))
      (fn [inner-child] (child-watch ret inner-child)))
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Output Collector captures children with the same output set, and only
;; releases new children for refined output sets.  

;; OutputCollector also handles decomposition and inside of state abstraction, when applicable.

(defn oc-name [inner-name] [:OC inner-name])


;; Note: must always wrap (at least with SA), or we lose context.
;; TODO: only :Atomic or :Pair inside, when SA off 
;;(defn wrapper? [sp] (#{:OC :SA} (first (sp-name sp))))
;; (comment  (if (wrapper? child-sp) child-sp (make-output-collecting-subproblem fs child-sp)))


(defn atomic-name-fs [n] (assert (= :Atomic (first n))) (second n))
(defn bind-ss [f [type ss]] [type (f ss)])
(defn log-input [fs inp-set] (if *state-abstraction* (bind-ss #(fs/get-logger fs %) inp-set) inp-set))
(defn get-input-key [fs inp-set] (if *state-abstraction* (bind-ss #(fs/extract-context fs %) inp-set) inp-set))

(declare get-ocs)

;; Input-key caching not necessary, but speeds things up a lot on, e.g., d-m.
(defn- make-output-collecting-subproblem [fs inp-key inner-sp]
  (make-wrapped-subproblem
   (oc-name (sp-name inner-sp)) (input-set inner-sp) #{:Atomic :Pair #_ ::TODO??? :SA :OC} inner-sp
   identity
   (fn child-watch [sp child-sp] 
     (if (fs/=-state-sets (second (get-output-set! inner-sp)) (second (get-output-set! child-sp)))
       (do (schedule-increase! sp) (connect-and-watch! sp child-sp nil #(child-watch sp %))) 
       (add-sp-child! sp (make-output-collecting-subproblem fs inp-key child-sp) :irrelevant))) 
   (fn oc-refine-input [s ni]
     (let [ninp-key (get-input-key fs ni)]
       (cond (= inp-key ninp-key) s
             (and *share-terminal* (solved-terminal? inner-sp) (= :opt (first inp-key)) (= :pess (first ni)))
               (let [r (summary/max-reward (sg/summary inner-sp))
                     ret (make-subproblem (oc-name (sp-name inner-sp)) ni nil
                           (fn [_] (throw (RuntimeException.)))
                           (fn [_ _] (throw (RuntimeException.)))
                           (fn [s] (make-summary (first ni) r :solved s r)))]
;                 (util/assert-is (and (= :opt (first inp-key)) (= :pess (first ni))) "%s" (def *bad* [inner-sp inp-key ninp-key]))
                 (set-output-set! ret [:pess (second (get-output-set! inner-sp))])
                 ret)               
             (= :Atomic (first (sp-name inner-sp)))
               (let [ret (get-ocs (sp-name inner-sp) fs ninp-key ni)]
                 (util/assert-is (not (identical? (canonicalize ret) inner-sp)) "%s" [(def *bad* [s inner-sp (input-set s) ni])])
                 (add-subsuming-sp! (canonicalize ret) inner-sp)
                 ret)  
             :else (make-output-collecting-subproblem fs ninp-key (refine-input inner-sp (log-input fs ni))))))))

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
(defn- make-state-abstracted-subproblem [fs inner-sp inp-set]
  (make-wrapped-subproblem
   (sa-name (sp-name inner-sp)) inp-set #{:OC} inner-sp
   (fn [o] (bind-ss #(fs/transfer-effects (second inp-set) %) o))
   (fn [sp child-sp] (add-sp-child! sp (make-state-abstracted-subproblem fs child-sp inp-set) :irrelevant)) 
   (fn [sp ni] (if (fs/=-state-sets (second ni) (second inp-set))
		 sp (make-state-abstracted-subproblem fs (refine-input inner-sp ni) ni)))))

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

(defn- refinement-names
  "Generate the names of subproblems representing refinements of fs from inp-set"
  [fs [t inp-set]]
  (assert (= t :opt)) ;; TODO: will need work for, e.g., when opt is blocked, pess not.
  (for [fs-seq (fs/child-seqs fs inp-set)]
    ((if *left-recursive* left-factor right-factor)
     (for [fs fs-seq]
       (let [in  (atomic-name fs)
             mid (if *collect-equal-outputs* (oc-name in) in)]
         (if *state-abstraction* (sa-name mid) mid))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)
(declare *pess-root*)

(defn- get-root-ts [inp-set fs] (sp-ts (make-atomic-subproblem fs [:opt inp-set] )))

(defn solve-opt* [henv choice-fn local?]
  (def *root* (apply get-root-ts (fs/make-init-pair henv)))
  (summary/solve
   #(sg/summary *root*)
   #_ #(let [s (sg/summary *root*)]
     (assert (not (= [-4 -4] ((juxt :wtd-rew :max-rew) s))))
     s)
   (sg/best-leaf-operator choice-fn local? evaluate-and-update!)
   #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n))))

(defn bind-simple-summary [inner-fn]
  (binding [*make-opt-summary* summary/make-simple-summary
            *make-opt-or*      (constantly #(sg/or-summarize % summary/or-combine-b))]
    (inner-fn)))

(defn solve-opt [henv choice-fn local?]
  (bind-simple-summary #(solve-opt* henv choice-fn local?)))




(defn implicit-dash-a*
  "Solve this hierarchical env using implicit DASH-A*, or variants thereupon.  Options are:
    :gather    Don't publish child subproblems with identical outputs?
    :d         Decomposition: cache and re-use subproblems by [name inp-set] pair?  Requires :gather.
    :s         State Abstraction: take state abstraction into account when caching?  Requires :d.
    :choice-fn Choose a child node to evaluate from alternatives (in sequence)
    :local?    Apply choice-fn recursively at each pair, or to an entire leaf sequence (slower)?
    :dir       Factor sequences into pairs using :left or :right recursion
    :prop      Automatically propagate subsumption from parents to matching children?
    :pess?     Use pessimistic bounds, or just optimistic ones? "
  [henv & {gather :gather d :d  s :s   choice-fn :choice-fn local? :local?  dir :dir   prop :prop solve-fn :solve-fn :as m
      :or {gather true   d true s true choice-fn last       local? true     dir :right prop true  solve-fn solve-opt}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir :prop :solve-fn} (keys m)))
  (when s (assert d))
  (when d (assert gather))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (case dir :left true :right false)
            *propagate-subsumption* prop]
    (solve-fn henv choice-fn local?)))


;; Alpha ranges from 0 to primitive to 1 for most high-level.
(declare *weight* *alpha-fn*)

(defn weight [n]
  (case (first n)
    (:OC :SA) (weight (second n))
    :Pair     (max (weight (nth n 1)) (weight (nth n 2)))
    :Atomic   (let [alpha (*alpha-fn* (first (fs/fs-name (second n))))]
                (util/assert-is (identity alpha) "unknown alpha: %s" n)
                (+ 1 (* alpha (- *weight* 1))))))


(defn bind-simple-weighted-summary [inner-fn]
  (binding [*make-opt-summary* (fn [r stat src] (summary/make-simple-weighted-summary r (weight (sp-name src))  stat src))
            *make-opt-or*      (fn [sp-name] (let [oc (summary/make-sws-or-combiner (weight sp-name))]
                                               #(sg/or-summarize % oc)))]
    (inner-fn)))

(defn solve-wtd [henv choice-fn local?]
  (bind-simple-weighted-summary #(solve-opt* henv choice-fn local?)))

(defn implicit-dash-wa* [henv w alpha-fn & opts]
  (binding [*weight* w
            *alpha-fn* alpha-fn]
    [(apply implicit-dash-a* henv (concat opts [:solve-fn solve-wtd]))
     :bound (summary/max-reward summary/*last-solution*)]))





;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  #_ 'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.implicit.dash-astar :as da] '[angelic.search.implicit.dash-astar-opt-old :as dao] '[angelic.search.summaries_old :as summaries-old] '[angelic.search.explicit.hierarchical :as his] '[angelic.search.implicit.dash-astar-opt-older :as dam]) (defn s [x]  (sg/summarize x)) (defn cs [x]  (sg/summary x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (sg/child-nodes x)))

;;(dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @sg/*summary-count*)) )))

;; (make-random-nav-switch-env 20 5 1) seems to be a difficult one for opt ... show off wtd.
;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather false :d false :s false :dir :right] h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 5 1) true)]   (time (println (run-counted #(identity (apply da/implicit-dash-wa* h 1.2 opts))) @sg/*summary-count*))  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*))   )))

;; Compare all four algs we have so far...
;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather true :d true :s :eager :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*))   (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*))   (time (println (run-counted #(identity (dam/implicit-random-dash-a*-opt h))) ))   (time (println (run-counted #(identity (his/explicit-simple-dash-a* h))) )) )))


;; Weighted A* on nav-switch

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather true :d false :s false :dir :right] h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 1) true)] (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*)) (time (println (run-counted #(identity (apply da/implicit-dash-wa* h 2 {:noop 0 'up 0 'down 0 'left 0 'right 0 'v 0 'h 0 'split-nav 0 'navv 0 'navh 0 'finish 0 'top 1 'act 1} opts))) @sg/*summary-count*)))))


;; Weighted A* on D-m

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather true :d true :s true :dir :right] h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*)) (time (println (run-counted #(identity (apply da/implicit-dash-wa* h 1.1 {'act 1 :discretem-tla 1 :move-to-goal 1 :go-grasp 0.8 :go-drop 0.8 :go-drop-at 0.4 :drop-at 0.3 :move-base 0.2 :nav 0.2 :reach 0.1 :putdown 0 :pickup 0 :gripper 0 :grasp 0 :park 0 :unpark 0 :base 0 'finish 0 :noop 0} opts))) @sg/*summary-count*)))))

;; With max-gap choice:
;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather true :d false :s false :dir :right] h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 1) true)] (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*)) (time (println (run-counted #(identity (apply da/implicit-dash-wa* h 2 {:noop 0 'up 0 'down 0 'left 0 'right 0 'v 0 'h 0 'split-nav 0 'navv 0 'navh 0 'finish 0 'top 1 'act 1} opts))) @sg/*summary-count*)))))

;; better settings
;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (debug 0 (let [opts [:gather true :d true :s true :dir :right] h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 6 3))]  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @sg/*summary-count*))  (time (println (run-counted #(identity (apply da/implicit-dash-wa* h 3.0 {'act 1 :discretem-tla 1.0 :move-to-goal 1 :go-grasp 0.7 :go-drop 0.7 :go-drop-at 0.6 :drop-at 0.4 :move-base 0.3 :nav 0.2 :reach 0.1 :putdown 0 :pickup 0 :gripper 0 :grasp 0 :park 0 :unpark 0 :base 0 'finish 0 :noop 0} (concat [:choice-fn (fn [s] (apply max-key (comp :max-gap sg/summary) s))] opts)))) @sg/*summary-count*)))))

;; TODO: failing at

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 4 3))]   (time (println (run-counted #(identity (da/implicit-dash-a* h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Graveyard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment ;; Stuff for making contextifying an output require an eval step (old -- needs fixup)
 (defn- make-deliberate-state-abstracted-subproblem [nm inner-sp inp-set]
   (if-let [out (get-output-set inner-sp)]
     (let [done? (atom false)  
           ret;; TODO!
           (traits/reify-traits
            [(simple-stub [:SA (stub-name inner-stub) in-set] in-set)]
            sg/Summarizable
            (summarize [s]
             (if @done? summary/+worst-simple-summary+
                 (make-summary inp-set nil (summary/max-reward (sg/summary (sp-ts out))) s)))   
            Evaluable
            (evaluate! [s] (reset! done? true)
             (set-stub-output! s (make-state-abstracted-subproblem s out))))]
       (sg/connect! ret out)
       ret)
     (make-eager-state-abstracted-subprolbem nm inner-sp inp-set)))

 (defn make-state-abstracted-subproblem [inner-sp inp-set]
   ((case *state-abstraction*
      :eager make-eager-state-abstracted-subproblem
      :deliberate make-deliberate-state-abstracted-subproblem)
    inner-sp inp-set)))


(comment
  
(defn solve-pess [opt-root choice-fn local?]
  (let [pess-root (sp-ts (refine-input (ts-sp opt-root) [:pess (second (input-set (ts-sp opt-root)))]))
        counter   (atom 0)]
    (def *pess-root* pess-root)
    (summary/solve
     #(do (assert (summary/interval-summary? (sg/summary pess-root)))
          (sg/summary (if (odd? (swap! counter inc)) opt-root pess-root)))
     (sg/best-leaf-operator choice-fn local? evaluate-and-update!)
     #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n)))))


(defn solve-wa* [opt-root choice-fn local?]
  (let [pess-root (sp-ts (refine-input (ts-sp opt-root) [:pess (second (input-set (ts-sp opt-root)))]))]
    (def *pess-root* pess-root)
    (summary/solve
     #(sg/summary pess-root)
     (sg/best-leaf-operator choice-fn local? evaluate-and-update!)
     #(let [[t in-name] (sp-name %)
            n (case t :OC (fs/fs-name (second in-name)) :Atomic (fs/fs-name in-name))]
        (when-not (= (first n) :noop) n)))))

(defn implicit-dash-wa* [henv w & opts]
  (binding [summary/*sws-weight* w
            *make-pess-summary*  summary/make-sw-summary]
    (apply implicit-dash-a* henv (concat opts [:solve-fn solve-wa*]))))

)