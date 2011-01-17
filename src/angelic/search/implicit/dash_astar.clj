(ns angelic.search.implicit.dash-astar
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

;; A revampting of dash_astar_opt, to move subsumption relationships and caching
;; out into a separate class.  This is necessary to keep pessimistic and optimistic
;; things in sync, and should help simplify and generalize subsumption stuff.

;; Here we replace all subsumption with consistency-maintaining and TDBs in summaries.
;; This simplifies problems with cycles that arrise when doing subsumption right.

;; Note: with good descriptions, subsumption/TDB has two purposes?
;;  1.  Give stubs a bound before evaluated.
;;  2.  Account for necessary inconsistency with implicit descriptions.


;; TODO: tests ! 

;;;;; Subsumption
;; TODO: Figure out why propagation isn't more helpful.
;; TODO: propagate to halves of pairs ?
;; TODO: more generic propagation?  (We know: names, subs. relationships on sets.  Efficient lookups?)
;; TODO: children wait on one (or more) subsumption parents.

;;;;; Pessimistic
;; TODO: add pessimistic variants (shared primitives)
;; TODO: bounding pressimistic descritpions (assume consistency for now)
;; TODO: hook up pess/opt with same input set?
;; TODO: pruning. 

;;;;; Tree construction
;; TODO: smarter output-collector (semantic) -- problems here though.
;; TODO: don't always split-left?
;; TODO: don't release children until they have lower reward or are primitive? 
;; TODO: make sure dead stuff can be GC'd
;; TODO: try holding back children until solved? 

;;;;; Summaries and solving 
;; TODO: lazy/pseudo-solve (regular seems impossible; bounds mean apparent decrease may be increase.
;;    I.e., live decrease -50 to -49, now blocked sibling becomes best; above is -50 TDB;
;; TODO: smarter summary updates (i.e., pass child)
;; TODO: smarter choose-leaf?
;; TODO: conspiracy number, weighted, etc.

;;;;; SP caching
;; TODO: tail (i.e., pair) caching? -- Only help for >2 len refs...
;; TODO: cache refine-inputs?
;; TODO: cache children of output-collector? ~15 examples >1 in dm 4-3...
;; TODO: investigate plan seq  normalization. (flattening)


;; Basic idea behind "wait on subsumption":
;;   Don't do anything with child of node with subs. parent
;;   until child has at least one subs. parent (or subs. parents are done.)
;; Can be implemented by not letting children go until they have subs...
;;  (and not incorporating into summary, except as bound) .... ?

(set! *warn-on-reflection* true)

(def *left-recursive*        true) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(def *collect-equal-outputs* true) ;; Collect identical output sets
(def *decompose-cache*       true) ;; nil for none, or bind to hashmap
(def *state-abstraction*     :eager ) ;; Or lazy or nil.
(def *propagate-subsumption* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;      Tree Summarizers      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol TreeSummarizer (ts-sp [ts]))

(defn- make-tree-summarizer [sp]
  (let [ret (traits/reify-traits [summaries/or-summarizable summaries/simple-cached-node]
              TreeSummarizer (ts-sp [ts] sp))]
    (summaries/connect! ret sp)
    (summaries/connect-subsumed! ret sp)
    ret))

(defmethod print-method angelic.search.implicit.dash_astar.TreeSummarizer [s o]
  (print-method (format "#<TS %s>" (print-str (ts-sp s))) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;         PubSubHub          ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord PubSubHub [^ArrayList subscribers ^ArrayList publications])
(defn make-pubsubhub [] (PubSubHub. (ArrayList.) (ArrayList.)))

(defn publications [psh] (doall (seq (:publications psh))))

(defn publish!     [psh pub]
  (.add ^ArrayList (:publications psh) pub)
  (doseq [sub (doall (seq (:subscribers psh)))] (sub pub)))

(defn subscribe!   [psh sub]
  (.add ^ArrayList (:subscribers psh) sub)
  (doseq [pub (doall (seq (:publications psh)))] (sub pub)))

;;;;;;;;;;;;;;;;;;;;;;;;;      Change Scheduling      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *increases* (ArrayList.))
(def *decreases* (ArrayList.))
(def *subsumes* (ArrayList.))

(defn schedule-increase! [sp] (.add ^ArrayList *increases* sp))
(defn schedule-decrease! [sp] (.add ^ArrayList *decreases* sp))
(defn schedule-subsumption! [ts subsumed-ts] (.add ^ArrayList *subsumes* [ts subsumed-ts]))

(defn do-changes! [^ArrayList a f] (doseq [sp a] (f sp)) (.clear a))

(declare evaluate!)

(defn evaluate-and-update! [s]
  (evaluate! s)
  (do-changes! *increases* summaries/summary-increased!) ;; Must go first for correctness.
  (do-changes! *subsumes* (fn [[ts subsumed-ts]] (summaries/connect-subsumed! ts subsumed-ts)))
  (do-changes! *decreases* summaries/summary-changed!))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Protocol  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here, inputs and outputs are [:opt/:pess actual-set] pairs.

(defprotocol Subproblem
  (sp-name             [s])
  (input-set           [s])
  (sp-ts               [s] "Summarizer that includes outputs/children.")
  (evaluate!           [s] "Evaluate or throw exception if not evaluable.")

  (get-output-set      [s]  "Return output or nil")
  (add-output-watcher! [s w] "Add watcher to be notified of self when has output.")
  (set-output-set!     [s o] "Internal. Set output set. ")

  (get-children        [s]  "List current outputs, for debugging only.")
  (add-child-watcher!  [s w] "Add a watcher to be notified of all child sps.")
  (add-sp-child!       [s o up?] "O is a subproblem child, possibly without output yet.
                                  Updates cost if up? and child must be held before publishing.")

  (publish-sp-child!   [s o] "Internal. O is a subproblem with output.  s must have output too.")
  (add-all-child-watcher! [s w] "Internal.  Get children, including unpublished ones.")

  (subsuming-sps       [s] "subproblems with same name, >= inp-set") 
  (add-subsuming-sp!   [s subsuming-sp]) 

  (refine-input        [s refined-input-set] "Return a child sp. Must have output."))

(defmethod print-method angelic.search.implicit.dash_astar.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s %s>" (System/identityHashCode sp) (sp-name sp)
                        (if (get-output-set sp) :OUT :STUB)) o))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Auxillary fns  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(defn get-output-set! [sp] (let [o (get-output-set sp)] (assert o) o))

(defn terminal? [sp]
  (and (empty? (get-children sp))
       (not (summary/live? (summaries/summary sp)))))

(defn solved-terminal? [sp]
  (and (empty? (get-children sp))
       (summary/solved? (summaries/summary sp))))

(defn- canonicalize [sp] (ts-sp (sp-ts sp)))

(defn- canonical? [sp] (identical? sp (ts-sp (sp-ts sp))))

(defn- connect-and-watch! [p c out-f child-f]
  (summaries/connect! p c)
  (when out-f (add-output-watcher! c out-f))
  (add-child-watcher! c child-f))

(defn- connect-and-watch-ts! [p c out-f]
  (summaries/connect! p (sp-ts c))
  (add-output-watcher! c out-f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Constructors  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Canonical SPs are Atomic and Pair; wrappers use TS of inner SP.

;; Summary-fn should take bound into account.
(defn- make-subproblem [nm inp-set wrapped-ts eval!-fn ri-fn summary-fn]
 (let [                 ts-atom          (atom wrapped-ts)
       ^PubSubHub       output-ps        (make-pubsubhub)
       ^PubSubHub       child-ps         (make-pubsubhub)
       ^PubSubHub       all-child-ps     (make-pubsubhub) ;; For sub-following -- remove if no help.
       ^IdentityHashMap subsuming-sp-set (IdentityHashMap.)]
  (traits/reify-traits [summaries/simple-cached-node]
   summaries/Summarizable (summarize [s] (summary-fn s))
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
  (add-sp-child!       [sp child-sp up?] ;; TODO: subsumption should prevent child from gettong output before parent ??
   (util/print-debug 2 "AC" sp child-sp)
   (when (canonical? sp)
     (schedule-subsumption! (sp-ts sp) (sp-ts child-sp))
     (publish! all-child-ps child-sp))   
   (if (and (get-output-set sp) (get-output-set child-sp))
    (publish-sp-child! sp child-sp)
    (do (summaries/connect! sp (sp-ts child-sp)) 
        (add-output-watcher! sp 
          (fn [_] (add-output-watcher! child-sp
                   (fn [_] (publish-sp-child! sp child-sp) 
                           (summaries/disconnect! sp (sp-ts child-sp))
                           (schedule-decrease! sp)))))
        (when up? (schedule-increase! sp)))))
  (publish-sp-child!      [s c] 
    (util/assert-is (and (not (identical? s c)) (get-output-set s) (get-output-set c)))
    (when (canonical? s)
      (summaries/connect! (sp-ts s) (sp-ts c))
      (schedule-increase! (sp-ts s)))    
    (publish! child-ps c))

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
      (when *propagate-subsumption*
        ;; TODO: efficiency, etc.
        (add-all-child-watcher! s
          (fn [child]
            (let [can-child (canonicalize child)]
              (add-all-child-watcher! subsuming-sp
                (fn [subsuming-child]
                  (let [can-subsuming-child (canonicalize subsuming-child)]
                    (when (= (sp-name can-child) (sp-name can-subsuming-child))
                      (when (add-subsuming-sp! can-child can-subsuming-child)
                        #_ (println [s subsuming-sp] "==>" [child subsuming-child])
                        )))))))))
      true))
  
  (refine-input    [s ni]
    (let [ret (ri-fn s ni)]
      (util/assert-is (= nm (sp-name ret)))
      (when (canonical? s) (add-subsuming-sp! ret s))
      ret)))))

(defmulti get-subproblem (fn get-subproblem-dispatch [nm inp] (first nm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare refinement-names)

(defn atomic-name [fs] [:Atomic fs])

(defn apply-description [fs [type inp-set]]
  (when-let [[out-set reward] ((case type :opt fs/apply-opt :pess fs/apply-pess) fs inp-set)]
    [[type out-set] reward]))

(defn make-summary [[inp-t] reward bound status src]
  (case inp-t
    :opt  (summary/make-simple-summary (if reward (min reward bound) bound) status src)
    :pess (summary/make-interval-summary (or reward Double/NEGATIVE_INFINITY) bound status src)))

;; Pess should have bound, then eval
;; -- cannot use add-bound!
;; Difference is that even if no pess set, we should be live.
;;  (summary should be other way...)
;; Pair has to be able to deal with no pess set...
;; For now, it should just not instantiate right
;; cleaner way to do this ???

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-subproblem [fs inp-set]
  (let [nm    (atomic-name fs)
        state (atom :ready) ;; set to out-set after first eval, then :go after second.
        sm-fn (atom #(make-summary inp-set nil (summaries/get-bound %) :live %))
        set-sm! (fn [s f] (do (reset! sm-fn f) (schedule-decrease! s)))] 
    (make-subproblem
     nm inp-set nil
     (fn evaluate! [s]
       (util/print-debug 1 "eval" nm (= :ready @state))
       (assert (not (= :go @state)))
       (if (= :set @state)
         (let [out-set @state] ;; Go live with chilren
           (reset! state :go)
           (if-let [subsuming-sps (seq (filter #(not (terminal? %)) (subsuming-sps s)))]
             (connect-and-watch! s (apply min-key (comp summaries/get-bound sp-ts) subsuming-sps) nil
               (fn [sub-out] (add-sp-child! s (refine-input sub-out inp-set) true))) 
             (doseq [ref-name (refinement-names fs inp-set)] #_ (println fs ref-name)
               (add-sp-child! s (get-subproblem ref-name inp-set) false))) 
           (set-sm! s summaries/or-summary))         
         (if-let [[out-set reward] (apply-description fs inp-set)]
           (let [status (fs/status fs (second inp-set))] ;; TODO: pess?
             (set-output-set! s out-set)
             (set-sm! s #(make-summary inp-set reward (summaries/get-bound %) status %))
             (reset! state (if (= status :live) :set :go)))
           (do (reset! state :go) ;; Die
               (summaries/add-bound! s Double/NEGATIVE_INFINITY)))))
     (fn [s ri] #_ (assert (not *collect-equal-outputs*)) ;; TODO: put back?
       (if (= ri inp-set) s (get-subproblem nm  ri)))
     (fn summarize [s] (@sm-fn s)))))

(defmethod get-subproblem :Atomic [[_ fs :as n] inp-set] 
  (make-atomic-subproblem fs inp-set))          

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Pair      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn pair-name [l r] [:Pair l r])

;; TODO: short circuit when left terminal?
;;   Except, when we get left output we still don't know, under current scheme ...
;; TODO: no right output when right blocked? 
(defn- make-pair-subproblem
  ([left-sp right-sp] (make-pair-subproblem left-sp (sp-name right-sp) (constantly right-sp)))
  ([left-sp right-name right-sp-fn]
;     (println "mps" left-sp right-name) (Thread/sleep 10)
     (let [nm (pair-name (sp-name left-sp) right-name)
           right-sp (delay (right-sp-fn (get-output-set! left-sp)))
           right?-atom (atom false) ;; Expand on right            
           ss (summaries/make-sum-summarizer nil)
           go-right! (fn [s] 
                       (reset! right?-atom true)                          
                       (summaries/disconnect! ss (sp-ts @right-sp))
                       (add-child-watcher! left-sp (fn [c] (def *bad* [s c]) (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch! ss @right-sp nil
                         (fn right-child [right-child] (add-sp-child! s (make-pair-subproblem left-sp right-child) true)))
                       (summaries/summary-changed-local! ss))
           ret (make-subproblem nm (input-set left-sp) nil 
                 (fn eval! [s] (schedule-decrease! s) (go-right! s)) ;; TODO: ??
                 (fn [s ni] (if (= ni (input-set left-sp)) s
                                (make-pair-subproblem (refine-input left-sp ni)
                                                      right-name #(refine-input @right-sp %))))
                 (fn [s] 
                   (or (and (not @right?-atom)
                            (solved-terminal? left-sp)
                            (if (empty? (get-children @right-sp))
                              (do (go-right! s) nil)
                              (let [r (min (summary/max-reward (summaries/summary ss)) (summaries/get-bound s))]
                                (make-summary (input-set left-sp) nil r :live s))))
                       (summaries/or-summary s))))]    
       (summaries/connect! ret ss)
       (connect-and-watch! ss left-sp
         (fn left-output [_]
           (connect-and-watch-ts! ss @right-sp (fn [o] (set-output-set! ret o)))
           (schedule-decrease! ss))
         (fn left-child [left-child]
           (add-sp-child! ret (make-pair-subproblem left-child right-name #(refine-input @right-sp %)) true))) 
       ret)))


(defmethod get-subproblem :Pair [[_ left-name right-name :as n] inp]
  (make-pair-subproblem (get-subproblem left-name inp) right-name #(get-subproblem right-name %)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-wrapped-subproblem [nm inp-set prefix-set inner-sp output-wrap child-watch ri-fn]
  (util/assert-is (contains? prefix-set (first (sp-name inner-sp))))
  (let [ret (make-subproblem nm inp-set (sp-ts inner-sp)
                             (fn [_] (throw (RuntimeException.)))
                             ri-fn summaries/or-summary)]
    (connect-and-watch! ret inner-sp
      (fn [o] (set-output-set! ret (output-wrap o)))
      (fn [inner-child] (child-watch ret inner-child)))
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn oc-name [inner-name] [:OC inner-name])

(defn- =-state-sets [[_ s1] [_ s2]]
  (util/assert-is (= (state/current-context s1) (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

;; Note: must always wrap (at least with SA), or we lose context.
;; TODO: only :Atomic or :Pair inside, when SA off 
;;(defn wrapper? [sp] (#{:OC :SA} (first (sp-name sp))))
;; (comment  (if (wrapper? child-sp) child-sp (make-output-collecting-subproblem fs child-sp)))

(declare get-ocs)

(defn atomic-name-fs [n] (assert (= :Atomic (first n))) (second n))
(defn bind-ss [[type ss] f] [type (f ss)])
(defn log-input [fs inp-set] (if *state-abstraction* (bind-ss #(fs/get-logger fs %) inp-set) inp-set))
(defn get-input-key [fs inp-set] (if *state-abstraction* (bind-ss #(fs/extract-context fs %) inp-set) inp-set))

;; Input-key caching not necessary, but speeds things up a lot on, e.g., d-m.
(defn- make-output-collecting-subproblem [fs inp-key inner-sp]
  (make-wrapped-subproblem
   (oc-name (sp-name inner-sp)) (input-set inner-sp) #{:Atomic :Pair #_ ::TODO??? :SA :OC} inner-sp
   identity
   (fn child-watch [sp child-sp] ;     (println sp child-sp (def *bad* [sp child-sp]))
     (if (=-state-sets (get-output-set! inner-sp) (get-output-set! child-sp))
       (do (schedule-increase! sp) (connect-and-watch! sp child-sp nil #(child-watch sp %))) 
       (add-sp-child! sp (make-output-collecting-subproblem fs inp-key child-sp) :irrelevant))) 
   (fn refine-input [s ni]
     (let [ninp-key (get-input-key fs ni)]
       (if (= inp-key ninp-key)
         s
         (if (= :Atomic (first (sp-name inner-sp)))
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

(defn sa-name [inner-name] [:SA inner-name])

(declare make-state-abstracted-subproblem)

;; Note: subsumed subproblems can have different irrelevant vars
(defn- make-eager-state-abstracted-subproblem [fs inner-sp inp-set]
  (make-wrapped-subproblem
   (sa-name (sp-name inner-sp)) inp-set #{:OC} inner-sp
   (fn [o] (bind-ss #(state/transfer-effects inp-set %) o))
   (fn [sp child-sp] (add-sp-child! sp (make-eager-state-abstracted-subproblem fs child-sp inp-set) :irrelevant)) 
   (fn [sp ni] (if (=-state-sets ni inp-set) sp (make-eager-state-abstracted-subproblem fs (refine-input inner-sp ni) ni)))))


(declare make-deliberate-state-abstracted-subproblem)
(comment TODO
 (defn- make-deliberate-state-abstracted-subproblem [nm inner-sp inp-set]
   (if-let [out (get-output-set inner-sp)]
     (let [done? (atom false)  
           ret;; TODO!
           (traits/reify-traits
            [(simple-stub [:SA (stub-name inner-stub) in-set] in-set)]
            summaries/Summarizable
            (summarize [s]
             (if @done? summary/+worst-simple-summary+
                 (make-summary inp-set nil (summary/max-reward (summaries/summary (sp-ts out))) s)))   
            Evaluable
            (evaluate! [s] (reset! done? true)
             (set-stub-output! s (make-state-abstracted-subproblem s out))))]
       (summaries/connect! ret out)
       ret)
     (make-eager-state-abstracted-subprolbem nm inner-sp inp-set))))

(defn make-state-abstracted-subproblem [inner-sp inp-set]
  ((case *state-abstraction*
     :eager make-eager-state-abstracted-subproblem
     :deliberate make-deliberate-state-abstracted-subproblem)
   inner-sp inp-set))

(defmethod get-subproblem :SA [[_ inner-n :as n] inp-set]
  (let [fs (atomic-name-fs (second inner-n))] 
    (make-eager-state-abstracted-subproblem fs (get-subproblem inner-n inp-set) inp-set)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Refinement Names     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- wrapped-atomic-name [fs]
  (let [in  (atomic-name fs)
        mid (if *collect-equal-outputs* (oc-name in) in)]
    (if *state-abstraction* (sa-name mid) mid)))

(defn- left-factor [is]
  (loop [s (next is) ret (first is)]
    (if s (recur (next s) (pair-name ret (first s))) ret)))

(defn- right-factor [[f & r]]
  (if (seq r) (pair-name f (right-factor r)) f))

(defn- refinement-names [fs [t inp-set]]
  (assert (= t :opt))
  (for [fs-seq (fs/child-seqs fs inp-set)]
    ((if *left-recursive* left-factor right-factor)
     (map wrapped-atomic-name fs-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)
(declare *pess-root*)

(defn solve-opt [root choice-fn local?]
  (summary/solve
   #(summaries/summary root)
   (summaries/best-leaf-operator choice-fn local? evaluate-and-update!)
   #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n))))

(defn solve-pess [opt-root choice-fn local?]
  (let [pess-root (refine-input (ts-sp opt-root) [:pess (second (input-set (ts-sp opt-root)))])]
    (def *pess-root* pess-root)
    (summary/solve
     #(summaries/summary opt-root)
     (summaries/best-leaf-operator choice-fn local? evaluate-and-update!)
     #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n)))))

(defn- get-root-ts [inp-set fs] (sp-ts (make-atomic-subproblem fs [:opt inp-set] )))

(defn implicit-dash-a*
  [henv & {gather :gather d :d   s :s    choice-fn :choice-fn local? :local?  dir :dir   prop :prop pess? :pess? :as m
      :or {gather true   d true s :eager choice-fn last       local? true     dir :right prop true  pess? true}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir :prop} (keys m)))
  (assert (contains? #{:left :right} dir))
  (assert (contains? #{nil false :eager :deliberate} s))
  (when s (assert d))
  (when d (assert gather))
;  (assert (contains? #{:uncached :lazy :eager  :eager-nosub :eager-nokids} c))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (= dir :left)
            *propagate-subsumption* prop]
    (def *root* (apply get-root-ts (fs/make-init-pair henv)))
    ((if pess? solve-pess solve-opt) *root* choice-fn local?)))












;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.implicit.dash-astar :as da] '[angelic.search.implicit.dash-astar-opt :as dao] '[angelic.search.summaries_old :as summaries-old] '[angelic.search.explicit.hierarchical :as his] '[angelic.search.implicit.dash-astar-monolithic :as dam]))

;; (require )
;;(do (defn s [x]  (summaries/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (summaries/child-nodes x)))

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) )))


; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (time (println (run-counted #(identity (da/implicit-dash-a* h :gather false :d false :s nil))) @summaries/*summary-count* @da/*out-count*)) (time (println (run-counted #(identity (dao/implicit-dash-a*-opt h :gather false :d false :s nil))) @summaries/*summary-count*  @dao/*out-count*)) )))




;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [opts [:gather false :d false :s nil :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 2 4))]  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @summaries/*summary-count* @da/*out-count*))  (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*  @dao/*out-count*)) )))
;; fails


;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [opts [:gather false :d false :s nil :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 1 4))]  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @summaries/*summary-count* @da/*out-count*))  (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*  @dao/*out-count*)) )))

;; Compare all four algs we have so far...
;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [opts [:gather true :d true :s :eager :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @summaries/*summary-count* @da/*out-count*))   (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*  @dao/*out-count*))   (time (println (run-counted #(identity (dam/implicit-random-dash-a*-monolithic h))) @summaries-old/*summary-count*  @dao/*out-count*))   (time (println (run-counted #(identity (his/explicit-simple-dash-a* h))) @summaries-old/*summary-count*  @dao/*out-count*)) )))




