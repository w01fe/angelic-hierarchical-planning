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

;; All TODOs from dash_astar_opt also apply here.

;; TODO: SP has hash table from (state-abstracted context) input set to stub (?).

;; TODO: tests ! 

;; TODO first: propagate subsumption links.
;; TODO second: add pessimistic variant. (primitives shared!)

;; TODO: bounding of pessimistic descriptions ? (assume consistency for now).

;; One basic kinds of subsumption propagation:
;;   X --> Y ==> for all child keys k, child(X, k) --> child(Y, k)
;;   This taken into account for atomic, not pairs now.

;; --> TODO: every SP should watch all subsuming SPs for children with matching
;;     names, add these as subsumption parents.
;; (Except any direct parents)

;; TODO: investigate plan seq  normalization. (flattening)
;; TODO: put back kill
;; TODO: figure out cause of comodification for children, e.g., d-m 3-3 -- seems to be pair

;; What's happening now is that output gets set for atomic;
;; that flows up, eventually triggers summary-changed! at pair.
;; That forces summaries all the way down --
;;  and children are somehow in inconsistent state.
;; (because children are ready and queued, but not released -- and
;;  not summarized either.  Cannot queue like we are now!)

;; Can we produce children before we have output?  Does anyone care?
;; Or, rather, do we need to run updates with output ?

;; TODO: missing updates on children -- need to think up a consistent scheme
;; Ways summary change can be initiated --
;;  sending out a child?
;;  receiving a child?
;;  explicit bound changes
;;  explicit summary changed initiations ...
;; (Output, not for now...)

;; Various protocols we could do
;; Require output before children?
;; Require children have output?
;; In interest of limiting branching, both seem like good ideas.

;; One issue: when I add a child right now, I may not update summary at all.
;;  That might be fine, except that
;;   (1) nobody may have computed summary child -- this means that pair splitting won't happen
;;   (2) child *can* actually spell increase, when solved ! .
;; TODO: just add *check-consistency* function ???

;; OK!  Basic goal of all this nonsense:
;;  --> Make sure all updates are made.
;;    --> Roots: evaluated SP, "freed" child, "captured" child (solved only?)
;;  --> Make sure no updates see an inconsistent state.
;; (made more challenging by fact that outputs can trigger children,
;;  children can trigger updates, updates can trigger more children (from pair), ...).
;; However, nothing can trigger outputs except outputs and evaluation.
;;  -- and children which create pair children that get outputs. . .. .
;; IF we just remove latter dependency, can do all tree modifications, then all updates.
;; We try to manage this now, but potentially fail.
;;  Alternative is old way, with summary-changed-local!
;; Or, a combination -- although not clear how S-C-L helps then...

;; Clearly, problem is with solved.
;; Can we propagate solved first, or something?
;; Can clearly propagate just solved info.  Doing it with summaries seems awkward.
;; If we do this right, could lead to solution to lazy problem as well ...?
;; Nah, summary is just too closely tied to status. (i.e., OC is solved if MAX-REWARD child is SOLVED)
;; This makes any sort of separate "solved-signal" painful -- including fresh outputs

;; Without the pair thing, we could do all our propagation.
;; Then, do subsumption connections, then update things with new children (incr),
;;  and finally update the evaluated leaf and anyone who gave up children (dec).
;; (where, exactly, should evaluated leaf go in this???).
;; (subsumption may be do more than we want, though).

;; Then, only problem is pair thing.
;; That will always happen in "increase" phase.
;; Problem: pair cannot return a correct status until it shifts and
;; potentially spits out new outputs.
;; Solution(?) -- we can still defer the decreases.
;; I.e., do al the increases first?
;; This is always guaranteed to be safe...?
;; This means that we always have to leave tree in consistent state-- Ugh.

;; Another idea: just try to make sure each operation is consistent, instead of batching everything.
;; I.e., release a child or output, wait for it to be fully "absorbed", do updates, then release next, etc.

;; Or, we can try to break dependence of pair on summary, e.g., by pushing solved as output.

;; Or, we can prevent further tree modifications by pair switch.
;; For instance, iff right has outputs already, it becomes live, must be evaluated to switch directions.

;; We can even take this one step further & do it automatically.

;; Forget about OC and 

;; Or, we can



(set! *warn-on-reflection* true)

(def *left-recursive*        true) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(def *collect-equal-outputs* true) ;; Collect identical output sets
(def *decompose-cache*       true) ;; nil for none, or bind to hashmap
(def *state-abstraction*     :eager ) ;; Or lazy or nil.
(def *propagate-subusmption* false)


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

;;;;;;;;;;;;;;;;;;;;;;;;;      Change Scheduling      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *increases* (ArrayList.))
(def *decreases* (ArrayList.))
(def *subsumes* (ArrayList.))

(defn schedule-decrease! [sp] (.add ^ArrayList *decreases* sp))
(defn schedule-increase! [sp] (.add ^ArrayList *increases* sp))
(defn schedule-subsumption! [ts subsumed-ts] (.add ^ArrayList *subsumes* [ts subsumed-ts]))



(defn do-changes! [^ArrayList a f]
  (doseq [sp a] (f sp))
  (.clear a))

(declare evaluate!)

;; Note: doing pairs right away doesn't help.
(defn evaluate-and-update! [s]
  (evaluate! s)
  (do-changes! *increases* summaries/summary-increased!) ;; Must go first for correctness.
  (do-changes! *subsumes* (fn [[ts subsumed-ts]] (summaries/connect-subsumed! ts subsumed-ts)))
  (do-changes! *decreases* summaries/summary-changed!))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Protocol  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem
  (sp-name             [s])
  (input-set           [s])
  (sp-ts               [s] "Summarizer that includes outputs/children.")
  (evaluate!           [s] "Evaluate or throw exception if not evaluable.")

  (get-output-set      [s]  "Return output or nil")
  (add-output-watcher! [s w] "Add watcher to be notified of self when has output.")

  (get-children        [s]  "List current outputs, for debugging only.")
  (add-child-watcher!  [s w] "Add a watcher to be notified of all child sps.")

  (subsuming-sps       [s] "subproblems with same name, >= inp-set") 
  (add-subsuming-sp!   [s subsuming-sp]) 

  (refine-input        [s refined-input-set] "Return a child sp. Must have output.")

  
  ;; Internal interface
  (add-sp-child!*      [s o] "O is a subproblem.  sw may have an updated summary,
                              but will not call summary-changed! on its parents.
                              The receiver is responsible for handling this change.
                              This allows handling decrease+increase in lock-step. ")
  (set-output-set!    [s o] "Set output set. "))

(defn get-output-set! [sp] (let [o (get-output-set sp)] (assert o) o))

(defn terminal? [sp]
  (and (empty? (get-children sp))
       (not (summary/live? (summaries/summary sp)))))

(defn solved-terminal? [sp]
  (and (empty? (get-children sp))
       (summary/solved? (summaries/summary sp))))


(defmethod print-method angelic.search.implicit.dash_astar.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s %s>" (System/identityHashCode sp) (sp-name sp)
                        (if (get-output-set sp) :OUT :STUB)) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Generic Trait  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *out-count* (atom 1))

(defn canonicalize [sp] (ts-sp (sp-ts sp)))
(defn canonical? [sp] (identical? sp (ts-sp (sp-ts sp))))

(defn notify-output-set! [w s] #_ (println "NO" s w) (w))
(defn notify-child! [w s c] #_ (println "NC" s c w) (swap! *out-count* inc) (w c))

(traits/deftrait simple-subproblem
  [nm inp-set wrapped-ts eval!-fn ri-fn]
  [                 ts-atom          (atom wrapped-ts)
   ^ArrayList       output-watchers  (ArrayList.)
                    out-set-atom     (atom nil)
   ^ArrayList       child-watchers   (ArrayList.)
   ^ArrayList       child-list       (ArrayList.)
   ^IdentityHashMap subsuming-sp-set (IdentityHashMap.)]
  [summaries/simple-cached-node]
  Subproblem
  (sp-name             [s] nm)
  (input-set           [s] inp-set)
  (sp-ts               [s] (or @ts-atom (reset! ts-atom (make-tree-summarizer s))))
  (evaluate!           [s] (eval!-fn s))
  
  (get-output-set      [s] @out-set-atom)
  (add-output-watcher! [s w] (if @out-set-atom (notify-output-set! w s) (.add output-watchers w)))
  (set-output-set!    [s o]
    (util/print-debug 2 "SO" s)
    (assert (nil? @out-set-atom))
    (reset! out-set-atom o)
    (doseq [w output-watchers] (notify-output-set! w s)))
  
  (get-children        [s] (doall (seq child-list)))
  (add-child-watcher!  [s w]
    (.add child-watchers w)                   
    (when (get-output-set s)) (doseq [c (get-children s)] (notify-child! w s c)))
  (add-sp-child!*      [s c] 
    (util/assert-is (and (not (identical? s c)) (get-output-set s) (get-output-set c)))
    (.add child-list c)
    (when (canonical? s)
      (summaries/connect! (sp-ts s) (sp-ts c))
      (schedule-increase! (sp-ts s)))    
    (doseq [w (doall (seq child-watchers))] (swap! *out-count* inc) (w c)))

  (subsuming-sps [s] (keys subsuming-sp-set))
  (add-subsuming-sp! [s subsuming-sp]
    (util/assert-is (canonical? s))
    (util/assert-is (canonical? subsuming-sp))                     
    (util/assert-is (= nm (sp-name subsuming-sp)))
    (util/assert-is (not (identical? s subsuming-sp)))
    (when-not (.containsKey subsuming-sp-set subsuming-sp)
      (.put subsuming-sp-set subsuming-sp true)
      (schedule-subsumption! (sp-ts subsuming-sp) (sp-ts s))))
  
  (refine-input    [s ni] (let [ret (ri-fn s ni)] (util/assert-is (= nm (sp-name ret))) ret)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Utils  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- connect-and-watch! [p c out-f child-f]
  (summaries/connect! p c)
  (when out-f (add-output-watcher! c out-f))
  (add-child-watcher! c child-f))

(defn- connect-and-watch-ts! [p c out-f]
  (summaries/connect! p (sp-ts c))
  (if (get-output-set c)
    (do (out-f) false)
    (do (add-output-watcher! c out-f) true)))

;;; TODO: why does changing to ts of child matter when assert on ??
;; TODO: subsumption should prevent child from gettong output before parent ??
(defn- add-sp-child! [sp child-sp up?]
   (util/print-debug 2 "AC" sp child-sp)
;  (println sp child-sp) (Thread/sleep 100)
   (when (canonical? sp)
     (schedule-subsumption! (sp-ts sp) (sp-ts child-sp))
    ;; TODO: propagate!
     )
   (if (and (get-output-set sp) (get-output-set child-sp))
    (add-sp-child!* sp child-sp)
    (do (summaries/connect! sp (sp-ts child-sp)) ;; Be safe; child could have children before we get output.
        (add-output-watcher! sp 
          (fn [] (add-output-watcher! child-sp
                   (fn [] (util/assert-is (get-output-set sp) "%s" [sp child-sp])
;                     (assert (empty? (get-children child-sp)))
                     (add-sp-child!* sp child-sp) 
                     (summaries/disconnect! sp (sp-ts child-sp))
                     (schedule-decrease! sp)))))
        (when up? (schedule-increase! sp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Constructors  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn noeval [s] (throw (RuntimeException. (print-str s "not evaluable!"))))

(defn make-wrapped-subproblem [nm inp-set prefix-set inner-sp output-wrap child-watch ri-fn]
  (util/assert-is (contains? prefix-set (first (sp-name inner-sp))))
  (let [ret (traits/reify-traits
             [summaries/or-summarizable
              (simple-subproblem nm inp-set (sp-ts inner-sp) noeval ri-fn)])]
    (connect-and-watch! ret inner-sp
      (fn [] (set-output-set! ret (output-wrap (get-output-set! inner-sp))))
      (fn [inner-child] (child-watch ret inner-child)))
    ret))


;; Note: summary-fn should take subsuming-bound into account.
(defn- make-simple-subproblem [nm inp-set ri-fn eval-fn summary-fn]
  (traits/reify-traits
   [(simple-subproblem
     nm inp-set nil eval-fn
     (fn [s ni] ;; Note ni may have different context.
       (if (= ni inp-set) s
         (let [subsumed-sp (ri-fn s ni)]
           (add-subsuming-sp! subsumed-sp s)
           subsumed-sp))))]
   summaries/Summarizable (summarize [s] (summary-fn s))))

;; Get a fresh subproblem with the given name and input.
(defmulti get-subproblem (fn get-subproblem-dispatch [nm inp] (first nm)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare refinement-names)

(defn atomic-name [fs] [:Atomic fs])

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-subproblem [fs inp-set]
  (let [nm    (atomic-name fs)
        state (atom :ready) ;; set to out-set after first eval, then :go after second.
        sm-fn (atom #(summary/make-live-simple-summary (summaries/get-bound %) %))] 
    (make-simple-subproblem
     nm inp-set
     (fn [s ri] (assert (not *collect-equal-outputs*)) (get-subproblem nm  ri))
     (fn evaluate! [s]
       (util/print-debug 1 "eval" nm (= :ready @state))
       (assert (not (= :go @state)))
       (if (not (= :ready @state))
         (let [out-set @state] ;; Go live with chilren
           (reset! state :go)
           (set-output-set! s out-set)
           (if-let [subsuming-sps (seq (filter #(not (terminal? %)) (subsuming-sps s)))]
             (connect-and-watch! s (apply min-key (comp summaries/get-bound sp-ts) subsuming-sps)
               (fn ignore-output [] nil)
               (fn [sub-out] (add-sp-child! s (refine-input sub-out inp-set) true))) 
             (doseq [ref-name (refinement-names fs inp-set)] #_ (println fs ref-name)
               (add-sp-child! s (get-subproblem ref-name inp-set) false))) 
           (reset! sm-fn summaries/or-summary)
           (schedule-decrease! s))         
         (if-let [[out-set reward] (fs/apply-opt fs inp-set)]
           (let [status (fs/status fs inp-set)]
             (if (= status :live)
               (do (reset! state out-set) ;; Wait to generate children
                   (summaries/add-bound! s reward))
               (do (reset! state :go) ;; Fixed (blocked/solved)
                   (reset! sm-fn #(summary/make-simple-summary (min (summaries/get-bound %) reward) status %))
                   (set-output-set! s out-set)
                   (schedule-decrease! s)))) ;; TODO? 
           (do (reset! state :go) ;; Die
               (summaries/add-bound! s Double/NEGATIVE_INFINITY)))))     
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
           ri-fn    (fn [s ni] (make-pair-subproblem (refine-input left-sp ni) right-name #(refine-input @right-sp %)))
           ss (summaries/make-sum-summarizer nil)
           go-right! (fn [s] 
                       (reset! right?-atom true)                          
                       (summaries/disconnect! ss (sp-ts @right-sp))
                       (add-child-watcher! left-sp (fn [c] (def *bad* [s c]) (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch! ss @right-sp
                         (fn ignore-output [] nil) 
                         (fn right-child [right-child] (add-sp-child! s (make-pair-subproblem left-sp right-child) true)))
                       (summaries/summary-changed-local! ss))
           ret (make-simple-subproblem nm (input-set left-sp) ri-fn
                 (fn eval! [s] (schedule-decrease! s) (go-right! s)) ;; TODO: ??
                 (fn [s] 
                   (or (and (not @right?-atom)
                            (solved-terminal? left-sp)
                            (if (empty? (get-children @right-sp))
                              (do (go-right! s) nil)
                              (do (summary/make-live-simple-summary
                                (min (summary/max-reward (summaries/summary ss)) (summaries/get-bound s)) s))))
                       (summaries/or-summary s))))]    
       (summaries/connect! ret ss)
       (connect-and-watch! ss left-sp
         (fn left-output []
           (connect-and-watch-ts! ss @right-sp 
             (fn [] (set-output-set! ret (get-output-set! @right-sp))))
           (schedule-decrease! ss))
         (fn left-child [left-child]
           (add-sp-child! ret (make-pair-subproblem left-child right-name #(refine-input @right-sp %)) true))) 
       ret)))


(defmethod get-subproblem :Pair [[_ left-name right-name :as n] inp]
  (make-pair-subproblem (get-subproblem left-name inp) right-name #(get-subproblem right-name %)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn oc-name [inner-name] [:OC inner-name])

(defn- =-state-sets [s1 s2]
  (util/assert-is (= (state/current-context s1) (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

;; Note: must always wrap (at least with SA), or we lose context.
;; TODO: only :Atomic or :Pair inside, when SA off 
;;(defn wrapper? [sp] (#{:OC :SA} (first (sp-name sp))))
;; (comment  (if (wrapper? child-sp) child-sp (make-output-collecting-subproblem fs child-sp)))

(declare get-ocs)

(defn atomic-name-fs [n] (assert (= :Atomic (first n))) (second n))
(defn log-input [fs inp-set] (if *state-abstraction* (fs/get-logger fs inp-set) inp-set))

(defn get-input-key [fs inp-set] (if *state-abstraction* (fs/extract-context fs inp-set) inp-set))
(defn get-cache-key [atomic-n inp-set] [atomic-n (get-input-key (atomic-name-fs atomic-n) inp-set)])

;; Input-key caching not necessary, but speeds things up a lot on, e.g., d-m.
(defn- make-output-collecting-subproblem [fs inp-key inner-sp]
  (make-wrapped-subproblem
   (oc-name (sp-name inner-sp)) (input-set inner-sp) #{:Atomic :Pair #_ ::TODO??? :SA :OC} inner-sp
   identity
   (fn child-watch [sp child-sp] ;     (println sp child-sp (def *bad* [sp child-sp]))
     (if (=-state-sets (get-output-set! inner-sp) (get-output-set! child-sp))
       (do (schedule-increase! sp) (connect-and-watch! sp child-sp nil #(child-watch sp %))) ;; TODO: ???
       (add-sp-child! sp (make-output-collecting-subproblem fs inp-key child-sp) false)))
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
   #(do ;      (assert (= (state/current-context %) (fs/precondition-context-set fs inp-set)))
        (state/transfer-effects inp-set %))
   (fn [sp child-sp] (add-sp-child! sp (make-eager-state-abstracted-subproblem fs child-sp inp-set) false)) 
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
                           (summary/make-live-simple-summary
                            (summary/max-reward (summaries/summary (sp-ts out))) s)))   
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

(defn- refinement-names [fs inp-set]
  (for [fs-seq (fs/child-seqs fs inp-set)]
    ((if *left-recursive* left-factor right-factor)
     (map wrapped-atomic-name fs-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- get-root-summarizer [inp-set fs] (sp-ts (make-atomic-subproblem fs inp-set )))

(def *lazy-cache* false) 
(def *no-subsumption* false)
(def *assume-consistency* false) ;; Don't propagate lazy increases.

;; TODO: sa options...
(defn implicit-dash-a*
  [henv & {gather :gather d :d   s :s    choice-fn :choice-fn local? :local?  dir :dir :as m
      :or {gather true   d true s :eager choice-fn last       local? true     dir :right}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir} (keys m)))
  (assert (contains? #{:left :right} dir))
  (assert (contains? #{nil false :eager :deliberate} s))
  (when s (assert d))
  (when d (assert gather))
;  (assert (contains? #{:uncached :lazy :eager  :eager-nosub :eager-nokids} c))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (= dir :left)
 ;            summaries/*cache-method* c
            ]
    (summaries/solve
     (apply get-root-summarizer (fs/make-init-pair henv))
     choice-fn local? evaluate-and-update!
     #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n)))))



;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (require '[angelic.search.implicit.dash-astar :as da] '[angelic.search.implicit.dash-astar-opt :as dao] '[angelic.search.summaries_old :as summaries-old])
;;(do (defn s [x]  (summaries/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (summaries/child-nodes x)))

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) )))


; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (time (println (run-counted #(identity (da/implicit-dash-a* h :gather false :d false :s nil))) @summaries/*summary-count* @da/*out-count*)) (time (println (run-counted #(identity (dao/implicit-dash-a*-opt h :gather false :d false :s nil))) @summaries/*summary-count*  @dao/*out-count*)) )))




;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [opts [:gather false :d false :s nil :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 2 4))]  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @summaries/*summary-count* @da/*out-count*))  (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*  @dao/*out-count*)) )))
;; fails


;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! summaries-old/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [opts [:gather false :d false :s nil :dir :right] h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 1 4))]  (time (println (run-counted #(identity (apply da/implicit-dash-a* h opts))) @summaries/*summary-count* @da/*out-count*))  (time (println (run-counted #(identity (apply dao/implicit-dash-a*-opt h opts))) @summaries-old/*summary-count*  @dao/*out-count*)) )))








(comment
 (def *pears* (IdentityHashMap.))
 (defn add-pear! [sp] (.put ^IdentityHashMap *pears* sp true))
 (defn steal-pears! [] (let [ret (doall (map identity (keys ^IdentityHashMap *pears*)))] (.clear ^IdentityHashMap *pears*) ret))
 #_(loop [pears (seq (steal-pears!))]
     (when pears  (doseq [p pears] (evaluate-and-update! p)) (recur (seq (steal-pears!))))))