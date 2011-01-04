(ns angelic.search.implicit.fah-astar-eval2
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
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

;; TODO: organize
;; TODO: remove extra stub indirection step when not needed?
;; (i.e., either reverse directions, or just have get-stub-output when known..)
;; TODO: pessimistic

;; TODO: pseudo-solve
;; TODO: smarter summary updates (i.e., pass child)
;; TODO: halfway eager prop -- eager about cost, not contents.
;; TODO: stepped state abstraction.

;; TODO: improve top-down propagation of bounds
;; TODO: better subusmption.

;; TODO: way to select traits without recompiling...
;; TODO: think about relation to old dash_astar_summary --
;;   i.e. where did excluded-child-set go ?
;;   where did output-constraints go ?


(set! *warn-on-reflection* true)


(def *no-identical-nonterminal-outputs* true)
(def *decompose-cache*     true) ;; nil for none, or bind to hashmap
(def *state-abstraction*   :eager) ;; Or lazy or nil.

(assert (contains? #{nil :eager :lazy} *state-abstraction*))
(when *state-abstraction* (assert *decompose-cache*))
(when *decompose-cache* (assert *no-identical-nonterminal-outputs*)) 

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

(traits/deftrait simple-watched
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)]
  []
  Watched
  (add-watcher! [sw w] #_(println :AW sw w) 
    (.add watchers w) 
    (doseq [o (doall (seq outputs))] (swap! *out-count* inc) (w o)) )
  (add-output! [sw o] ;               (println :AO sw o) (Thread/sleep 10)
    (.add outputs o)
    (doseq [w (doall (seq watchers))] (swap! *out-count* inc) (w o)))
  (get-outputs [sw] (doall (seq outputs))))

(defn connect-and-watch! [p c f]
  (summaries/connect! p c false)
  (add-watcher! c f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Stubs     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Stub
  (stub-name   [s])
  (input-set   [s]))

(traits/deftrait simple-stub [name inp] [] [summaries/simple-cached-node simple-watched]
  Stub (input-set [s] inp)
       (stub-name [s] name))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))


;; Stub must implement Summarizable, optionally implements Evaluable

(defprotocol Evaluable (evaluate! [s]))
(defn can-evaluate? [s] (instance? angelic.search.implicit.fah_astar_eval2.Evaluable s))

(defn set-stub-output! [stub sp]
  (assert (empty? (get-outputs stub)))
  (summaries/summary-changed-local! stub)
  (add-output! stub sp))

(comment (defn get-stub-output [s] (util/safe-singleton (get-outputs s))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return any outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn subproblem-name [s] (stub-name (stub s)))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (subproblem-name sp)) o))


(defn connect-subsuming! [child subsuming-sp]
  (when subsuming-sp (summaries/connect! child (tree-summarizer subsuming-sp) true)))

(defn add-sp-child! [sp child-sp]
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

(defn tree-summarizer? [s] (instance? angelic.search.implicit.fah_astar_eval2.TreeSummarizer s))

(defn make-tree-summarizer [init-bound]
 (let [tdb-atom (atom init-bound)]
   (traits/reify-traits [summaries/simple-cached-node]
     TreeSummarizer (top-down-bound [s] @tdb-atom)
                    (add-top-down-bound! [s b]
                      (when (< b @tdb-atom) ;; ;; Note: adding < current max-reward actually hurts...
                        (reset! tdb-atom b)
                        (doseq [c (summaries/node-ordinary-children s)]
                          (when (tree-summarizer? c)
                            (add-top-down-bound! c b)))
                        (summaries/summary-changed! s)))    
     summaries/Summarizable (summarize [s] (summaries/or-summary s @tdb-atom)))))

(defn init-tree-summarizer! [ts inner-sp subsuming-sp]
  (connect-and-watch! ts inner-sp
    (fn [child-sp]
      (summaries/connect! ts (tree-summarizer child-sp) false)
      (add-top-down-bound! (tree-summarizer child-sp) (top-down-bound ts))
      (summaries/summary-changed! ts))) ;; TODO: speedup by checking child reward? 
  (connect-subsuming! ts subsuming-sp))

(defn get-inner-sp [ts]
  (->> (summaries/node-ordinary-children ts)
       (remove tree-summarizer?)
       util/safe-singleton))

(defn ts-str [sp])
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer [ts o]
  (let [stub (stub (get-inner-sp ts))]
    (print-method (format "#<TS$%8h %s>" (System/identityHashCode stub) (stub-name stub)) o)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-subproblem
  [stb out-set ts term? ri-fn] []
  [summaries/simple-cached-node simple-watched]
  Subproblem (stub            [s] stb)
             (output-set      [s] out-set)
             (tree-summarizer [s] ts)
             (terminal?       [s] term?)
             (refine-input    [s ni] (ri-fn s ni)))


(defn make-simple-subproblem [stub subsuming-sp out-set terminal? summary-fn ri-fn init-bound]
  (let [ts  (make-tree-summarizer init-bound)
        ret (traits/reify-traits [(simple-subproblem stub out-set ts terminal? ;; Note ni may have different context.
                                                     (fn [s ni] (if (= ni (input-set stub)) stub (ri-fn s ni))))]
              summaries/Summarizable (summarize [s] (summary-fn s (top-down-bound ts))))]
    (init-tree-summarizer! ts ret subsuming-sp)
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: simplify these, avoid extra stub steps when possible ?

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: collect children too ?
(declare make-output-collecting-subproblem)
(defn make-output-collecting-stub [inner-stub]
  (assert (not (= (first (stub-name inner-stub)) :OS)))
  (assert (not (= (first (stub-name inner-stub)) :SA)))  
  (let [in-set (input-set inner-stub)
        ret (traits/reify-traits [summaries/or-summarizable (simple-stub [:OS (stub-name inner-stub) in-set] in-set)])]
    (connect-and-watch! ret inner-stub #(set-stub-output! ret (make-output-collecting-subproblem ret %)))
    ret))


(defn =-state-sets [s1 s2]
  (util/assert-is (= (state/current-context s1) (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

;; TODO: is refine-input right ?
(defn make-output-collecting-subproblem [stb inner-sp]
  (let [ts  (tree-summarizer inner-sp)
        ret (traits/reify-traits ;; TODO: RI correct?
             [(simple-subproblem stb (output-set inner-sp) ts false #(refine-input inner-sp %2))]
             summaries/Summarizable (summarize [s] (summaries/or-summary s (top-down-bound ts))))]
    (connect-and-watch! ret inner-sp
      (fn child-watch [o]
        (if (=-state-sets (output-set inner-sp) (output-set o))
          (do (connect-and-watch! ret o child-watch)
              (summaries/summary-changed! ret))
          (do (if (#{:SA :OS} (first (stub-name (stub o)))) 
                (add-sp-child! ret o)
                (connect-and-watch! ret (make-output-collecting-stub (stub o)) #(add-sp-child! ret %)))))))    
    ret))

;;;;;;;;;;;;;;;;;;;;;;;;;;;     State Abstraction     ;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-state-abstracted-subproblem)
(defn make-state-abstracted-stub [inner-stub in-set]
  (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub [:SA (stub-name inner-stub) in-set] in-set)])]
    (connect-and-watch! ret inner-stub #(set-stub-output! ret (make-state-abstracted-subproblem ret %)))
    ret))

;; Note: subsumed subproblems can have different irrelevant vars
(defn make-state-abstracted-subproblem [stb inner-sp]
  (let [ts  (tree-summarizer inner-sp)
        in  (input-set stb)
        out (state/transfer-effects in (output-set inner-sp))
        ri-fn #(if (=-state-sets %2 in) stb (refine-input inner-sp %2))
        ret (traits/reify-traits
             [summaries/or-summarizable (simple-subproblem stb out ts (terminal? inner-sp) ri-fn)])]
    (connect-and-watch! ret inner-sp
      (fn [o] (connect-and-watch! ret (make-state-abstracted-stub (stub o) in) #(add-sp-child! ret %))))    
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
                (connect-and-watch! ret (refine-input sub-out inp-set) #(add-sp-child! ret %))
                (summaries/summary-changed! ret))) ;; TODO: needed?                       
            ret)
          
          :else 
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false summaries/or-summary ri-fn reward)]
            (doseq [child (map #(make-fs-seq-stub inp-set %) (fs/child-seqs function-set inp-set))]
              (connect-and-watch! ret child #(add-sp-child! ret %)))
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
;; TODO: do something more with subsuming?
(defn- get-atomic-stub [subsuming-sp inp-set function-set]
  (let [full-name [:Atomic (fs/fs-name function-set)
                   (if *state-abstraction* (fs/extract-context function-set inp-set) inp-set)]
        make-stub #(let [r (make-atomic-stub [:Atomic (fs/fs-name function-set)] subsuming-sp % function-set)]
                     (if *no-identical-nonterminal-outputs* (make-output-collecting-stub r) r))]
    (if-let [^HashMap dc *decompose-cache*]
      (if *state-abstraction*
        (let [stub (util/cache-with dc full-name (make-stub (fs/get-logger function-set inp-set)))]
          (make-state-abstracted-stub stub inp-set))   
        (util/cache-with dc full-name (make-stub inp-set)))
     (make-stub inp-set))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)

;; TODO: fix up subsuming, parent, etc.
;; nils at bottom should chase subsuming-sp.
;; TODO TODO: we should not use tree-summarizer when left-done
;; How do we know that current output set is actually solved ?
;; TODO: remove ss ?
;; Note: this is the only place logic depends on summary.  Potential for problems? 
(defn- make-pair-subproblem [subsuming-sp pair-stub left-sp right-sp]
  (let [expand-right? (not (or (summary/live? (summaries/summary left-sp)) (seq (get-outputs left-sp))))
        [ss watch stub-f]
        (if expand-right?
          [(summaries/make-sum-summarizer [(tree-summarizer left-sp) right-sp])
           right-sp #(make-pair-stub2 nil left-sp (stub %))]
          [(summaries/make-sum-summarizer [left-sp (tree-summarizer right-sp)])
           left-sp #(make-pair-stub2 nil % (refine-input right-sp (output-set %)))])
        ret (make-simple-subproblem
             pair-stub subsuming-sp (output-set right-sp) false             
             (if (or expand-right? (not *no-identical-nonterminal-outputs*)) summaries/or-summary
                 (let [left-done? (atom false)]
                   (fn [s b] 
                     (when (and (not @left-done?)
                                (not (summary/live? (summaries/summary left-sp)))
                                (not (= Double/NEGATIVE_INFINITY (summary/max-reward (summaries/summary left-sp))))) ;; TODO:??
                       (reset! left-done? true) #_(println "BOO" pair-stub left-sp right-sp (class right-sp))
                       (summaries/disconnect! s ss)
                       (add-watcher! left-sp (fn [o] (def *sum* [s left-sp o])
                                               (throw (RuntimeException. "Solved and children."))))
                       ;; TODO: do more efficiently?
                       (connect-and-watch! s (make-pair-stub2 subsuming-sp left-sp (stub right-sp))
                                           (fn [os] (connect-and-watch! s os #(add-sp-child! s %))))
 ;                       (add-sp-child! s (make-pair-subproblem subsuming-sp pair-stub left-sp right-sp))
                       )
                     (summaries/or-summary s b))))             
             (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                          (subproblem-name right-sp) #(refine-input right-sp %)))
             0)]

    (summaries/connect! ret ss false)
    
    (add-watcher! watch
      (fn [o]
        (summaries/summary-changed-local! ss)
        (connect-and-watch! ret (stub-f o) #(add-sp-child! ret %))
        (summaries/summary-changed! ret))) ;; TODO: efficiency?
    
    ret))

;; TODO: remove children as they are no longer needed ?
(defn- make-pair-stub2 [subsuming-sp left-sp right-stub]
  (let [ret (traits/reify-traits
             [summaries/sum-summarizable
              (simple-stub [:Pair (subproblem-name left-sp) (stub-name right-stub)]
                           (input-set (stub left-sp)))])]
    (connect-subsuming! ret subsuming-sp)
    (summaries/connect! ret (tree-summarizer left-sp) false)
    (connect-and-watch! ret right-stub 
      #(set-stub-output! ret (make-pair-subproblem subsuming-sp ret left-sp %)))
    ret))

(defn- make-pair-stub1 [subsuming-sp left-stub right-name right-stub-fn]
  (let [ret (traits/reify-traits [summaries/or-summarizable
                                  (simple-stub [:Pair1 (stub-name left-stub) right-name]
                                               (input-set left-stub))])]
    (connect-subsuming! ret subsuming-sp)
    (connect-and-watch! ret left-stub 
      (fn [lo]
        (connect-and-watch! ret
          (make-pair-stub2 subsuming-sp lo (right-stub-fn (output-set lo)))
          #(set-stub-output! ret %))
        (summaries/summary-changed! ret))) ;; TODO: wasteful?
    
    ret))


(defn- make-fs-seq-stub
  ([inp-set fs] (make-fs-seq-stub inp-set fs (map fs/fs-name fs)))
  ([inp-set [first-fs & rest-fs] fs-names]
     (let [left-stub (get-atomic-stub nil inp-set first-fs)]
       (if (empty? rest-fs)
         left-stub
         (make-pair-stub1 nil left-stub (rest fs-names)
                          #(make-fs-seq-stub % rest-fs (rest fs-names)))))))


  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil nil inp-set fs)]
    (dotimes [_ 2] (evaluate! root-stub))
    (util/safe-singleton (get-outputs root-stub))))

(defn implicit-fah-a*-eval2 [henv]
  (binding [summaries/*cache-method* :lazy
            *decompose-cache* (when *decompose-cache* (HashMap.))]
    (summaries/solve
     (tree-summarizer (apply get-root-subproblem (fs/make-init-pair henv)))
     #(evaluate! (last (filter can-evaluate? %)))
     #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n)))))

; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.fah-astar-eval2 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (do (def s summaries/summarize) (def sc summary/children) (def nc summaries/node-ordinary-children) (def src summary/source))
;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)) )))



; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-fah-a*-eval2 h))) @summaries/*summary-count* @*out-count*)) )))





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



