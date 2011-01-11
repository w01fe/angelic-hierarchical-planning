(ns angelic.search.implicit.dash-astar-opt
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summaries_old :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList]))

;; A version of eval subproblems where we explicitly represent the relationships
;; between subproblems, and allow "listeners" that wait for a subproblem to be
;; evaluated.

;; Breaks down into "subproblems" with well-defined action seqs, inputs, outputs,
;; and "stubs" where output is not known yet.
;; Summary of either represents child subproblems not yet produced, or if "solved",
;; a terminal state with the current output.

;; Here we properly deal with weirdness of stubs/inner-sps decreaseing as they add
;; children, by makig sure to do the updates synchronously.

;; Compared to old dash_astar_summary:
;;  excluded-child-set went away, since we're now eager about pushing new outputs
;;   output-constraints went away since we have refine-input.

;; Note: these are out-of-date, before new summary infrastructure.
;; Timing breakdown on DM 4-3 is:
;; 10% extract-leaf-seq
;; 20% lfss-empty?
;; 20% optimistic-set-and-reward
;; 25% make-atomic-subproblem (immediate refs+)
;; 30% summary-changed

;; Actually just about 1/3 in apply-opt, counting primitives, 10% in immediate-refs
;; (almost half in primitives -- close enough).

;; Explicit is still faster on small or easy instances, slower on hard ones.

;; TODO: find cleaner overall architecture.  Right now, names
;;   don't really do anything, and there's too much worrying about types, etc.
;;   Solution may be to have Generator (takes place of name) --> Stub --> SP.
;;   Generator knows how to take input set and produce stub., etc.
;;   For now, seems like too much complexity for too little gain.

;; TODO: think about how this actually works and what propagates.

;;;;; Features
;; --> TODO: pessimistic (problem: subsets & correspondence!)
;;      potential solution: revamp to separate following-plans
;;      and sets-of-reachable states.

;; TODO: smarter choose-leaf?
;; TODO: don't always split-left?
;; TODO: smarter output-collector (semantic)

;;;;; Summaries and solving 
;; TODO: pseudo-solve
;; TODO: smarter summary updates (i.e., pass child)
;; TODO: enforce consistency across the board.
;; Note: regular lazy seems impossible, need at least some pseudo...
;;    Top-down bounds render these untenable, since an apparent decrease may be an increase? (See hard-dm 3-3)
;;    I.e., live decrease -50 to -49, now blocked sibling becomes best; above is -50 TDB;

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; TODO: actually, top-down bounds break a lot of things -- ?
;;   I.e., if we have TDB, blocked status can hide behind unblocked, expand things needlessly.
;;   How can we fix this?
;;   ;; (This includes subsumption parents, as well).
;;   One could try to build top-down bounding into all summaries ... but
;;   it may actually be unfixable, in the presence of sums
;;    (keeping bounds across sums means downwards updates with every up...)

;; Note: with good descriptions, subsumption/TDB has two purposes?
;;  1.  Give stubs a bound before evaluated.
;;  2.  Account for necessary inconsistency with implicit descriptions.

;;;;; SP caching
;; TODO: tail (i.e., pair) caching? -- Only help for >2 len refs...
;; TODO: cache refine-inputs?
;; TODO: cache children of output-collector? ~15 examples >1 in dm 4-3...

;;;;; Misc
;; TODO: investigate building seqs right-to-left.
;; TODO: garbage collect dead stuff
;; TODO: improve top-down propagation of bounds
;; TODO: better subusmption.

;; TODO: why doesn't subsumption help (at all?)
;; Note: subsumption edges don't help AT ALL, under seemingly any settings
;;       subsumption in atomic seems to help at most 50%, not at all with D/S.
;; Part of the reason is that top-down-bound seems to fill similar role -- removing both
;;   gives modest but small slowdown (x2)

;; TODO: tweak DM to be more interesting.
;; Descriptions are just too accurate ?? (problems too easy?) (state spaces too small?)
;; Descriptions, esp for move-to-goal, are far too expensive.



(set! *warn-on-reflection* true)


(def *left-recursive* true) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(def *collect-equal-outputs* true) ;; Collect identical output sets
(def *decompose-cache*       true) ;; nil for none, or bind to hashmap
(def *state-abstraction*     :eager ) ;; Or lazy or nil.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Watches      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stubs have at most one output (SP), SPs have any number

(defprotocol Watched
  (add-watcher! [s w] "Add a watcher to be notified of all outputs to this.
                       A watcher is just a fn of new-subproblem.")
  (add-output!  [sw o] "O is a subproblem.  sw may have an updated summary,
                        but will not call summary-changed! on its parents.
                        The receiver is responsible for handling this change.
                        This allows handling decrease+increase in lock-step. ")
  (get-outputs  [sw]  "List current outputs"))

(def *out-count* (atom 1))

(traits/deftrait watched-node
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)]
  [summaries/simple-cached-node]
  Watched
  (add-watcher! [sw w] #_(println :AW sw w) 
    (.add watchers w) 
    (doseq [o (doall (seq outputs))] (swap! *out-count* inc) (w o)) )
  (add-output! [sw o] ;               (println :AO sw o) (Thread/sleep 10)
    (.add outputs o)
    (doseq [w (doall (seq watchers))] (swap! *out-count* inc) (w o)))
  (get-outputs [sw] (doall (seq outputs))))

(defn- connect-and-watch! [p c f]
  (summaries/connect! p c false)
  (add-watcher! c f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Stubs     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Stub
  (stub-name   [s])
  (input-set   [s]))

(traits/deftrait simple-stub [name inp] [] [watched-node]
  Stub (input-set [s] inp)
       (stub-name [s] name))

(defmethod print-method angelic.search.implicit.dash_astar_opt.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))

;; Stub must implement Summarizable, optionally implements Evaluable

(defprotocol Evaluable (evaluate! [s]))
(defn- can-evaluate? [s] (instance? angelic.search.implicit.dash_astar_opt.Evaluable s))

(defn- set-stub-output! [stub sp]
  (assert (empty? (get-outputs stub)))
  (summaries/summary-changed-local! stub)
  (add-output! stub sp))


(defn- get-stub-output  [s] (first (get-outputs s)))
(defn- get-stub-output! [s] (util/safe-singleton (get-outputs s)))

;; Just give output directly if subproblem is ready
;; Return true if waiting
(defn- connect-and-watch-stub! [p c f]
  (assert (instance? angelic.search.implicit.dash_astar_opt.Stub c))
  (if-let [sp (get-stub-output c)]
    (do (f sp) false)
    (do (summaries/connect! p c false)
        (add-watcher! c f)
        true)))

;; Used when p needs update if c does not produce immediate output.
(defn- connect-and-watch-stub-up! [p c f]
  (when (connect-and-watch-stub! p c f) (summaries/summary-changed! p)))

(defn- make-wrapping-stub [[name in-set] inner-stub sp-fn]
  (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub name in-set)])]
    (connect-and-watch-stub! ret inner-stub #(set-stub-output! ret (sp-fn ret %)))
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return any outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn- subproblem-name [s] (stub-name (stub s)))

(defmethod print-method angelic.search.implicit.dash_astar_opt.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (subproblem-name sp)) o))


(defn- connect-subsuming! [child subsuming-sp]
  (when subsuming-sp (summaries/connect! child (tree-summarizer subsuming-sp) true)))

(defn- add-sp-child! [sp child-sp]
  (assert (not (terminal? sp)))
  (summaries/summary-changed-local! sp)
  (add-output! sp child-sp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; TODO: propagate top-down-bounds downward in smarter way using existing IS?
;; TODO: we need to make sure tree sums get called on add-output! first to ensure
;;       consistency with top-down-bounds ? 
;; TODO: top-down bound business does not actually help at all
;;  (except ensuring consistency if we're asserting it...)

(defprotocol TreeSummarizer
  (top-down-bound    [s])
  (add-top-down-bound! [s b]))

(defn- tree-summarizer? [s] (instance? angelic.search.implicit.dash_astar_opt.TreeSummarizer s))

(defn- make-tree-summarizer [init-bound]
 (let [tdb-atom (atom  init-bound)]
   (traits/reify-traits [summaries/simple-cached-node]
     TreeSummarizer (top-down-bound [s] @tdb-atom)
                    (add-top-down-bound! [s b]
                      (when (< b @tdb-atom) ;; ;; Note: adding < current max-reward actually hurts...
                        (reset! tdb-atom b)
                        (doseq [c (summaries/node-ordinary-children s)]
                          (when (tree-summarizer? c)
                            (add-top-down-bound! c b)))
                        (summaries/summary-changed! s)))    
     summaries/Summarizable (summarize [s] (summaries/or-summary s  @tdb-atom)))))

(defn- init-tree-summarizer! [ts inner-sp subsuming-sp]
  (connect-and-watch! ts inner-sp
    (fn [child-sp]
      (summaries/connect! ts (tree-summarizer child-sp) false)
      (add-top-down-bound! (tree-summarizer child-sp) (top-down-bound ts))
      (summaries/summary-changed! ts))) ;; TODO: speedup by checking child reward? 
  (connect-subsuming! ts subsuming-sp))

(defn- get-inner-sp [ts]
  (->> (summaries/node-ordinary-children ts)
       (remove tree-summarizer?)
       util/safe-singleton))

(defn- ts-str [sp])
(defmethod print-method angelic.search.implicit.dash_astar_opt.TreeSummarizer [ts o]
  (let [stub (stub (get-inner-sp ts))]
    (print-method (format "#<TS$%8h %s>" (System/identityHashCode stub) (stub-name stub)) o)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-subproblem [stb out-set ts term? ri-fn] [] [watched-node]
  Subproblem (stub            [s] stb)
             (output-set      [s] out-set)
             (tree-summarizer [s] ts)
             (terminal?       [s] term?)
             (refine-input    [s ni] (ri-fn s ni)))


(defn- make-simple-subproblem [stub subsuming-sp out-set terminal? summary-fn ri-fn init-bound]
  (let [ts  (make-tree-summarizer init-bound)
        ret (traits/reify-traits [(simple-subproblem stub out-set ts terminal? ;; Note ni may have different context.
                                                     (fn [s ni] (if (= ni (input-set stub)) stub (ri-fn s ni))))]
              summaries/Summarizable (summarize [s] (summary-fn s (top-down-bound ts))))]
    (init-tree-summarizer! ts ret subsuming-sp)
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-output-collecting-subproblem)
(defn- make-output-collecting-stub [inner-stub]
  (assert (not (= (first (stub-name inner-stub)) :OS)))
  (assert (not (= (first (stub-name inner-stub)) :SA)))
  (make-wrapping-stub
   [[:OS (stub-name inner-stub)] (input-set inner-stub)]
   inner-stub make-output-collecting-subproblem))


(defn- =-state-sets [s1 s2]
  (util/assert-is (= (state/current-context s1) (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

(defn- make-output-collecting-subproblem [stb inner-sp]
  (let [;        counter (HashMap.)
        ts  (tree-summarizer inner-sp)
        ret (traits/reify-traits 
             [(simple-subproblem stb (output-set inner-sp) ts false
                                 #(doto (if (= (input-set stb) %2) stb (refine-input inner-sp %2)) ;Needed when SA off
                                    (-> stub-name first #{:SA :OS} assert)))]
             summaries/Summarizable (summarize [s] (summaries/or-summary s (top-down-bound ts))))]
    (connect-and-watch! ret inner-sp
      (fn child-watch [o]
        (if (=-state-sets (output-set inner-sp) (output-set o))
          (do (connect-and-watch! ret o child-watch)
              (summaries/summary-changed! ret))
          (do #_ (let [c (.get counter (input-set (stub o)))]
                (when c (println c (stub-name (stub o))))
                (.put counter (input-set (stub o)) (inc (or c 0))))
              
              (if (#{:SA :OS} (first (subproblem-name o))) 
                (add-sp-child! ret o)
                (connect-and-watch-stub! ret (make-output-collecting-stub (stub o)) #(add-sp-child! ret %))))))) ;; No update needed
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;     State Abstraction     ;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-state-abstracted-subproblem)
(defn- make-eager-state-abstracted-stub [inner-stub in-set]
  (make-wrapping-stub [[:SA (stub-name inner-stub)] in-set] inner-stub make-state-abstracted-subproblem))


(defn- make-deliberate-state-abstracted-stub [inner-stub in-set]
  (if-let [out (get-stub-output inner-stub)]
    (let [done? (atom false)  
          ret
          (traits/reify-traits
           [(simple-stub [:SA (stub-name inner-stub) in-set] in-set)]
           summaries/Summarizable
           (summarize [s]
            (if @done? summary/+worst-simple-summary+
                (summary/make-live-simple-summary
                 (summary/max-reward (summaries/summary (tree-summarizer out))) s)))   
           Evaluable
           (evaluate! [s] (reset! done? true)
            (set-stub-output! s (make-state-abstracted-subproblem s out))))]
      (summaries/connect! ret out false)
      ret)
    (make-eager-state-abstracted-stub inner-stub in-set)))


(defn- make-state-abstracted-stub [inner-stub in-set]
  ((case *state-abstraction*
     :eager make-eager-state-abstracted-stub
     :deliberate make-deliberate-state-abstracted-stub)
   inner-stub in-set))


;; Note: subsumed subproblems can have different irrelevant vars
(defn- make-state-abstracted-subproblem [stb inner-sp]
  (let [ts  (tree-summarizer inner-sp)
        in  (input-set stb)
        out (state/transfer-effects in (output-set inner-sp))
        ri-fn #(if (=-state-sets %2 in) stb (refine-input inner-sp %2))
        ret (traits/reify-traits
             [summaries/or-summarizable (simple-subproblem stb out ts (terminal? inner-sp) ri-fn)])]
    (connect-and-watch! ret inner-sp
      (fn [o] (connect-and-watch-stub-up! ret (make-state-abstracted-stub (stub o) in) #(add-sp-child! ret %))))
    ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-fs-seq-stub get-atomic-stub)

(defn- make-atomic-subproblem [stub function-set subsuming-sp out-set reward status]
  (let [inp-set  (input-set stub)
        ri-fn    (fn [s ri] (get-atomic-stub s ri function-set))]
    (cond (not (= status :live))
          (make-simple-subproblem
           stub subsuming-sp out-set true
           (fn [s b] (summary/make-simple-summary (min b reward) status s)) ri-fn reward)
          
          (and subsuming-sp (not (terminal? subsuming-sp))) 
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false summaries/or-summary ri-fn reward)]
            (connect-and-watch! ret subsuming-sp
              (fn [sub-out]
                (connect-and-watch-stub-up! ret (refine-input sub-out inp-set) #(add-sp-child! ret %))))
            ret)
          
          :else 
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false summaries/or-summary ri-fn reward)]
            (doseq [child (map #(make-fs-seq-stub inp-set %) (fs/child-seqs function-set inp-set))]
              (connect-and-watch-stub! ret child #(add-sp-child! ret %)))
            ret))))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [name subsuming-sp inp-set function-set]
  (let [state (atom :ready) ;; set to [out-set reward] after first eval, then :go after second.
        ret
        (traits/reify-traits [(simple-stub name inp-set)]
         summaries/Summarizable
         (summarize [s]
           (cond (= :ready @state) (summary/make-live-simple-summary (summaries/subsuming-bound s) s)
                 (= :go    @state) summary/+worst-simple-summary+
                 :else             (summary/make-live-simple-summary
                                    (min (summaries/subsuming-bound s) (second @state)) s)))   
         Evaluable
         (evaluate! [s]
           (assert (not (= :go @state)))
           (let [ready? (= :ready @state)]
             (if-let [[out-set reward :as op] (if ready? (fs/apply-opt function-set inp-set) @state)]
               (let [status (if ready? (fs/status function-set inp-set)   :live)]
;                 (println "eval" s ready? status reward)
                 (if (or (not ready?) (not (= status :live)))
                   (do (reset! state :go)
                       (->> (make-atomic-subproblem s function-set subsuming-sp out-set reward status)
                            (set-stub-output! s)))
                   (do (reset! state op) (summaries/summary-changed! s))))
               (do (reset! state :go) (summaries/summary-changed! s))))))]
    (connect-subsuming! ret subsuming-sp)
    ret))

;; Note: we must always wrap in S-A stub to get effects out of logger. 
(defn- get-atomic-stub [subsuming-sp inp-set function-set]
  (let [full-name [:Atomic (fs/fs-name function-set)
                   (if *state-abstraction* (fs/extract-context function-set inp-set) inp-set)]
        make-stub #(let [r (make-atomic-stub [:Atomic (fs/fs-name function-set)] subsuming-sp % function-set)]
                     (if *collect-equal-outputs* (make-output-collecting-stub r) r))]
    (if-let [^HashMap dc *decompose-cache*]
      (if *state-abstraction*
        (let [stub (util/cache-with dc full-name (make-stub (fs/get-logger function-set inp-set)))]
          (make-state-abstracted-stub stub inp-set))   
        (util/cache-with dc full-name (make-stub inp-set)))
     (make-stub inp-set))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)

;; NOTE: subsumption doesn't seem to help
;; TODO: fix up subsuming, parent, etc.
;; nils at bottom should chase subsuming-sp.
;; Note: this is the only place logic depends on summary.  Potential for problems?
(defn- make-pair-subproblem [subsuming-sp pair-stub left-sp right-sp]
  (let [expand-right? (and (summary/solved? (summaries/summary left-sp)) (empty? (get-outputs left-sp)))
        kids (if expand-right? [(tree-summarizer left-sp) right-sp] [left-sp (tree-summarizer right-sp)])
        ss   (summaries/make-sum-summarizer kids)
        ret (make-simple-subproblem
             pair-stub subsuming-sp (output-set right-sp) false             
             (if (or expand-right? (not *collect-equal-outputs*)) summaries/or-summary
                 (let [left-done? (atom false)] ;; Manually take into account left-solved, when no output message.
                   (fn [s b] 
                     (when (and (not @left-done?) (summary/solved? (summaries/summary left-sp))) 
                       (reset! left-done? true) 
                       (summaries/disconnect! s ss)
                        ;; Make sure we don't double count, because child will use tree-summarizer of left.
                       (add-watcher! left-sp (fn [o] (def *sum* [s left-sp o])
                                               (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch-stub! s (make-pair-stub2 subsuming-sp left-sp (stub right-sp))
                                           (fn [os] (connect-and-watch! s os #(add-sp-child! s %))))) ;; no update needed                     
                     (summaries/or-summary s b))))             
             (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                          (subproblem-name right-sp) #(refine-input right-sp %)))
             0)]

    (summaries/connect! ret ss false)

    (let [[watch stub-f] (if expand-right?
                           [right-sp #(make-pair-stub2 nil left-sp (stub %))]
                           [left-sp #(make-pair-stub2 nil % (refine-input right-sp (output-set %)))])]
      (add-watcher! watch
         (fn [o]
           (summaries/summary-changed-local! ss)
           (connect-and-watch-stub-up! ret (stub-f o) #(add-sp-child! ret %)))))
    
    ret))

(comment
  ;; Old test used this -- do we need to split on right for blocked left?
  (not (summary/live? (summaries/summary left-sp)))                                
 (not (= Double/NEGATIVE_INFINITY (summary/max-reward (summaries/summary left-sp)))))

(defn- make-pair-stub2 [subsuming-sp left-sp right-stub]
  (let [nm [:Pair (subproblem-name left-sp) (stub-name right-stub)]
        is (input-set (stub left-sp))]
    (if (get-stub-output right-stub) ;; short-circuit the mess below
      (doto (make-wrapping-stub [nm is] right-stub #(make-pair-subproblem subsuming-sp %1 left-sp %2))
        (-> get-stub-output assert)) ;; summary of wrapping stub would be wrong, otherwise...
      (let [ret (traits/reify-traits [summaries/sum-summarizable (simple-stub nm is)])]
        (connect-subsuming! ret subsuming-sp)
        (summaries/connect! ret (tree-summarizer left-sp) false)
        (connect-and-watch-stub! ret right-stub 
            #(set-stub-output! ret (make-pair-subproblem subsuming-sp ret left-sp %)))
        ret))))

(defn- make-pair-stub1 [subsuming-sp left-stub right-name right-stub-fn]
  (if-let [left-sp (get-stub-output left-stub)]
    (make-pair-stub2 subsuming-sp left-sp (right-stub-fn (output-set left-sp)))
   (let [nm [:Pair1 (stub-name left-stub) right-name]
         is (input-set left-stub)
         ret (traits/reify-traits [summaries/or-summarizable (simple-stub nm is)])]
     (connect-subsuming! ret subsuming-sp)
     (connect-and-watch-stub! ret left-stub 
       (fn [lo]
         (connect-and-watch-stub-up! ret
           (make-pair-stub2 subsuming-sp lo (right-stub-fn (output-set lo)))
           #(set-stub-output! ret %))))
     ret)))


;; Experimental version -- switched order.
(defn- make-left-recursive-fs-seq-stub
  ([inp-set fs] (make-left-recursive-fs-seq-stub inp-set fs (map fs/fs-name fs)))
  ([inp-set [first-fs & rest-fs] fs-names]
     (loop [left-stub (get-atomic-stub nil inp-set first-fs) rest-fs rest-fs fs-names (rest fs-names)]
       (if (empty? rest-fs)
         left-stub
         (recur (make-pair-stub1 nil left-stub (first fs-names) #(get-atomic-stub nil % (first rest-fs)))
                (rest rest-fs) (rest fs-names))))))

(defn- make-right-recursive-fs-seq-stub
  ([inp-set fs] (make-right-recursive-fs-seq-stub inp-set fs (map fs/fs-name fs)))
  ([inp-set [first-fs & rest-fs] fs-names]
     (let [left-stub (get-atomic-stub nil inp-set first-fs)]
       (if (empty? rest-fs)
         left-stub
         (make-pair-stub1 nil left-stub (rest fs-names)
                          #(make-right-recursive-fs-seq-stub % rest-fs (rest fs-names)))))))

(defn- make-fs-seq-stub [inp-set fs]
  ((if *left-recursive* make-left-recursive-fs-seq-stub make-right-recursive-fs-seq-stub)
   inp-set fs))

  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil nil inp-set fs)]
    (dotimes [_ 2] (evaluate! root-stub))
    (get-stub-output! root-stub)))

(def *lazy-cache* false) 
(def *no-subsumption* false)
(def *assume-consistency* false) ;; Don't propagate lazy increases.

;; TODO: sa options...
(defn implicit-dash-a*-opt
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
     (tree-summarizer (apply get-root-subproblem (fs/make-init-pair henv)))
     choice-fn local? evaluate!
     #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n)))))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.dash-astar-opt 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar-opt 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (do (def s summaries/summarize) (def sc summary/children) (def nc summaries/node-ordinary-children) (def src summary/source))
;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a*-opt h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a*-opt h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a*-opt h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a*-opt h))) @summaries/*summary-count* @*out-count*)) )))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Graveyard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(comment
  (defn pseudo-solve [root-sp]
   (summaries/pseudo-solve root-sp summary/+worst-simple-summary+ (complement summaries/expanded?)
                           #(if (evaluated? %) (do (assert (not (summaries/expanded? %))) (child-keys %)) (evaluate! %))))

  
  (defn implicit-fah-a*-eval-pseudo [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       subproblem/pseudo-solve)))



