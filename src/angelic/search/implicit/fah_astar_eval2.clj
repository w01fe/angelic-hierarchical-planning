(ns angelic.search.implicit.fah-astar-eval2
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList]))

;; A version of eval subproblems where we explicitly represent the relationships
;; between subproblems, and allow "listeners" that wait for a subproblem to be
;; evaluated.

;; Here we properly deal with weirdness of stubs/inner-sps decreaseing as they add
;; children, by makig sure to do the updates synchronously.

;; TODO: improve top-down propagation of bounds
;; TODO: better subusmption.
;; TODO: diagnose inconsistency in d-m 2 3 

;; TODO: lump together children?  i.e., outside rather than inside solution?

;; Problem with decomposition: terminal subproblems get generated when
;; created, not when optimal.


;; Basic solution to both -- SP is optimally solved when tree summarizer
;; has status solved, by child other than inner-sp
;;  TODO: ties should be broken away from inner-sp.  Always?
;; SO: idea is to
;; -- Always publish if different output set
;; -- Otherwise, always add internally.
;; --  (to tree summarizer, if terminal, inner-sp otherwise)
;; -- When tree summarizer becomes solved by terminal output,
;;    -- publish this output
;;    -- and shut down publisher. --ie no more outputs.
;; To implement this, need:
;; - tie breaking (implement in summarize method?)
;; - notification of tree summarizer solved by ... (implement in summarize method?)


;; Breaks down into "subproblems" with well-defined action seqs, inputs, outputs,
;; and "stubs" where output is not known yet.
;; Summary of either represents child subproblems not yet produced.
;; These are produced into "tree summary", which has semantic view.

;; TODO: problem with decomposed on d-m 2-3 -- end up blocked?

;; TODO: general problem -- what if action we're refining input of gets
;; blocked deeper down?

(set! *warn-on-reflection* true)

;; TODO: note lazy is so lazy about subsumption , ...

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
  (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
 (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)

(def *no-identical-nonterminal-outputs* true )
(def *decompose-cache*   nil #_  true) ;; nil for none, or bind to hashmap  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Watched
  (add-watcher! [s w] "Add a watcher to be notified of all outputs to this.
                       A watcher is just a fn of new-subproblem.")
  (add-output!  [sw o]    "O is a subproblem")
  (get-outputs  [sw]))

;; Every watcher of a stub must also have it as an OR in its summary
;; (possibly added with something else).
;; Receiver of update is responsible for updating its summary --
;;  implicitly, watched's summary may have changed, without cascading up the tree
;; This allows changes in lock-step, so we don't end up with inconsistency problems.
;; (decrease + increase)

(traits/deftrait simple-watched
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)]
  []
  Watched
  (add-watcher! [sw w] #_(println :AW sw w) #_ (assert (not (some #(= % w) watchers)))
    (.add watchers w) 
    (doseq [o (doall (seq outputs))] (w o))#_ (println :WF sw))
  (add-output! [sw o] #_ (println :AO sw o) 
    (.add outputs o)
    (doseq [w (doall (seq watchers))] (w o)) #_(println :OF sw))
  (get-outputs [sw] (doall (seq outputs))))


;; Note: this entails zero minimum cost (i.e., nonnegative costs).
(defn subsuming-bound [s]
  (->> (summaries/node-subsuming-children s)
       (map (comp summary/max-reward summaries/summary))
       (apply min 0)))

(defn or-summary [s b]
  (swap! summaries/*summary-count* inc)
  (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s))
                      s (min (subsuming-bound s) b)))


(traits/deftrait or-summarizable [] [] []
  summaries/Summarizable (summarize [s] (or-summary s 0)))

(traits/deftrait simple-cached-node [] [] [summaries/simple-node cache-trait])

(defn sum-summary [s b]
  (swap! summaries/*summary-count* inc)
  (let [children (summaries/node-ordinary-children s)]
    (assert (= (count children) 2))
    (summary/+ (summaries/summary (first children)) (summaries/summary (second children))
               s (min b (subsuming-bound s)))))

(traits/deftrait sum-summarizable [] [] []
  summaries/Summarizable (summarize [s] (sum-summary s 0)))

(defn make-sum-summarizer [kids]
  (let [ret (traits/reify-traits [sum-summarizable simple-cached-node])]
    (doseq [kid kids] (summaries/connect! ret kid false))
    ret))




(defn connect-and-watch! [p c f]
  (summaries/connect! p c false)
  (add-watcher! c f))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Protocols     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Evaluable
  (evaluate!      [s]))

(defn can-evaluate? [s]
  (instance? angelic.search.implicit.fah_astar_eval2.Evaluable s))

;; Stub implements node, watched, possibly Evaluable, cached, Summarizable
;;  -- Has at most a single output.
;; Reward does not include output -- so stub + output reward gives consistent picture.
;; Watchers of stub must include it as OR- in their summaries.
;; Stubs cannot be subsumption children.
;; TODO: codify these constraints somehow. 

(defprotocol Stub
  (stub-name   [s])
  (input-set   [s]))

(traits/deftrait simple-stub [name inp] [] [] Stub (input-set [s] inp) (stub-name [s] name))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return further outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn subproblem-name [s] (stub-name (stub s)))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (subproblem-name sp)) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expects to be a parent of inside, but not have inside as a child.
;; All children are tree summarizers.
;; Non-subsuming children must be added by calling connect-child-sp!
(defprotocol TreeSummarizer
  (get-inner-sp      [ts] "Get subproblem for this ts")
  (top-down-bound    [s])
  (add-top-down-bound! [s b]))

;; TODO: propagate top-down-bounds downward in smarter way using existing IS?
;; TODO: we need to make sure tree sums get called on add-output! first to ensure
;;       consistency with top-down-bounds ? 
(defn make-tree-summarizer [inner-sp init-bound]
 (let [tdb-atom (atom init-bound)
       ret (traits/reify-traits [simple-cached-node]
            TreeSummarizer
            (get-inner-sp [ts] inner-sp)
            (top-down-bound [s] @tdb-atom)
            (add-top-down-bound! [s b]
             (when (< b @tdb-atom) ;; ;; Note: adding < current max-reward actually hurts...
               (reset! tdb-atom b)
               (doseq [c (summaries/node-ordinary-children s)]
                 (when (instance? angelic.search.implicit.fah_astar_eval2.TreeSummarizer c)
                   (add-top-down-bound! c b)))
               (summaries/summary-changed! s)))    
            summaries/Summarizable
            (summarize [s] (or-summary s @tdb-atom)))]
   (connect-and-watch! ret inner-sp
     (fn [child-sp]
       (summaries/connect! ret (tree-summarizer child-sp) false)
       (add-top-down-bound! (tree-summarizer child-sp) @tdb-atom)
       (summaries/summary-changed! ret))) ;; TODO: speedup? 
   ret))

(comment         (let [my-sum (summaries/summary ret)
                child-sum (summaries/summary (tree-summarizer child-sp))]
            (when-not (summary/>= my-sum child-sum)
              (summaries/summary-changed! ret))))




(defn ts-str [sp])
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer [ts o]
  (let [stub (stub (get-inner-sp ts))]
    (print-method (format "#<TS$%8h %s>" (System/identityHashCode stub) (stub-name stub)) o)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn set-stub-output! [stub sp]
  (summaries/summary-changed-local! stub)
  (add-output! stub sp))

;; Would be nice to assert consistency, but hard to get before-summary...
;; This version keeps children with same input inside.
;; Actually makes things worse sometimes (more evaluations?!) -- with first, better with last.
;; TODO: this solution does not work with decomposition -- infinite loops
;; TODO: the check commented out below works, but adds 50% overhead.
;; TODO: also, it doesn't seem to work... -- see dm 2-3
;;  (Since we don't keep only first solution)
(defn add-sp-child! [sp child-sp]
  (assert (not (terminal? sp)))
  (summaries/summary-changed-local! sp)
  (add-output! sp child-sp))


;; Note: All nonterminal subproblems use or-summary for ri-fn
(defn make-simple-subproblem
  [stub subsuming-sp out-set terminal? summary-fn ri-fn init-bound]
  (let [ts-atom (atom nil)
        ret (traits/reify-traits [simple-cached-node simple-watched]
             summaries/Summarizable (summarize       [s] (summary-fn s (top-down-bound @ts-atom)))
             Subproblem             (stub            [s] stub)
                                    (output-set      [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
                                    (terminal?       [s] terminal?)
                                    (refine-input    [s ni]
                                      (if (= ni (input-set stub)) stub (ri-fn s ni))))]
    (reset! ts-atom (make-tree-summarizer ret init-bound))
    (when subsuming-sp (summaries/connect! @ts-atom (tree-summarizer subsuming-sp) true))
    ret))

;; TODO: better grouping -- allow adding etc? 
(defn make-output-collecting-subproblem [inner-sp]
  (let [ts  (tree-summarizer inner-sp)
        ret (traits/reify-traits [simple-cached-node simple-watched ]
             summaries/Summarizable (summarize       [s] (or-summary s (top-down-bound ts)))
             Subproblem             (stub            [s] (stub inner-sp))
                                    (output-set      [s] (output-set inner-sp))
                                    (tree-summarizer [s] ts)
                                    (terminal?       [s] false)
                                    (refine-input    [s ni] (refine-input inner-sp ni)))
        child-watch (fn child-watch [o]
                      (if (= (output-set inner-sp) (output-set o))
                        (do (connect-and-watch! ret o child-watch)
                            (summaries/summary-changed! ret))
                        (add-sp-child! ret o)))]
    (connect-and-watch! ret inner-sp child-watch)    
    ret))

(defn output-wrap [sp]
  (if *no-identical-nonterminal-outputs*
    (make-output-collecting-subproblem sp)
    sp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;     Subproblem Types and Stubs     ;;;;;;;;;;;;;;;;;;;;;;;
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
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false or-summary ri-fn reward)]
            (connect-and-watch! ret subsuming-sp
              (fn [sub-out]
                (connect-and-watch! ret (refine-input sub-out inp-set) #(add-sp-child! ret %))
                (summaries/summary-changed! ret))) ;; TODO: needed?                       
            (output-wrap ret))
          
          :else 
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false or-summary ri-fn reward)]
            (doseq [child (map #(make-fs-seq-stub inp-set %) (fs/child-seqs function-set inp-set))]
              (connect-and-watch! ret child #(add-sp-child! ret %)))
            (output-wrap ret)))))




(defn connect-subsuming! [child subsuming-sp]
  (when subsuming-sp (summaries/connect! child (tree-summarizer subsuming-sp) true)))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [name subsuming-sp inp-set function-set]
  (let [state (atom :ready) ;; set to [out-set reward] after first eval, then :go after second.
        ret
        (traits/reify-traits
         [(simple-stub name inp-set)
          simple-watched simple-cached-node]
         summaries/Summarizable
         (summarize [s]
           (cond (= :ready @state) (summary/make-live-simple-summary (subsuming-bound s) s)
                 (= :go    @state) summary/+worst-simple-summary+
                 :else             (summary/make-live-simple-summary
                                    (min (subsuming-bound s) (second @state)) s)))   
         Evaluable
         (evaluate! [s]
;                    (println "evals" s)
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

;; TODO: do something more with subsuming?
(defn- get-atomic-stub [subsuming-sp inp-set function-set]
  (let [full-name [:Atomic (fs/fs-name function-set) inp-set]
        name [:Atomic (fs/fs-name function-set)]]
   (if *decompose-cache*
     (util/cache-with ^HashMap *decompose-cache* full-name
       (make-atomic-stub name subsuming-sp inp-set function-set))
     (make-atomic-stub name subsuming-sp inp-set function-set))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)


(defn can-split? [sp]
  (or (summary/live? (summaries/summary sp))
      (seq (get-outputs sp))))

;; TODO: fix up subsuming, parent, etc.
;; nils at bottom should chase subsuming-sp.
;; TODO TODO: we should not use tree-summarizer when left-done
;; How do we know that current output set is actually solved ?
;; TODO: remove ss ?
;; Note: this is the only place logic depends on summary.  Potential for problems? 
(defn- make-pair-subproblem [subsuming-sp pair-stub left-sp right-sp]
;  (println "mps" pair-stub)
  (let [expand-right? (not (can-split? left-sp) ) #_(terminal? left-sp)
        [ss watch stub-f]
        (if expand-right?
          [(make-sum-summarizer [(tree-summarizer left-sp) right-sp])
           right-sp #(make-pair-stub2 nil left-sp (stub %))]
          [(make-sum-summarizer [left-sp (tree-summarizer right-sp)])
           left-sp #(make-pair-stub2 nil % (refine-input right-sp (output-set %)))])
        ret (make-simple-subproblem
             pair-stub subsuming-sp (output-set right-sp) false             
             (if (or expand-right? (not *no-identical-nonterminal-outputs*)) or-summary
                 (let [left-done? (atom false)]
                   (fn [s b] 
                     (when (and (not @left-done?) (not (summary/live? (summaries/summary left-sp))))
                       (reset! left-done? true) #_(println "BOO" pair-stub left-sp right-sp (class right-sp))
                       (summaries/disconnect! s ss)
                       (add-watcher! left-sp (fn [o] (def *sum* [s left-sp o])
                                               (throw (RuntimeException. "Solved and children."))))
                       ;; TODO: do more efficiently?
                       (connect-and-watch! s (make-pair-stub2 subsuming-sp left-sp (stub right-sp))
                                           (fn [os] (connect-and-watch! s os #(add-child-sp! s %))))
 ;                       (add-sp-child! s (make-pair-subproblem subsuming-sp pair-stub left-sp right-sp))
                       )
                     (or-summary s b))))             
             (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                          (subproblem-name right-sp) #(refine-input right-sp %)))
             0)]

    (summaries/connect! ret ss false)
    
    (add-watcher! watch
      (fn [o]
        (summaries/summary-changed-local! ss)
        (connect-and-watch! ret (stub-f o) #(add-sp-child! ret %))
        (summaries/summary-changed! ret))) ;; TODO: efficiency?
    
    (output-wrap ret)))



;; TODO: remove children as they are no longer needed ?
(defn- make-pair-stub2 [subsuming-sp left-sp right-stub]
  (let [ret (traits/reify-traits
             [simple-cached-node simple-watched sum-summarizable
              (simple-stub [:Pair (subproblem-name left-sp) (stub-name right-stub)]
                            (input-set (stub left-sp)))])]
    (connect-subsuming! ret subsuming-sp)
    (summaries/connect! ret (tree-summarizer left-sp) false)
    (connect-and-watch! ret right-stub 
      #(set-stub-output! ret (make-pair-subproblem subsuming-sp ret left-sp %)))
    ret))

(defn- make-pair-stub1 [subsuming-sp left-stub right-name right-stub-fn]
  (let [ret (traits/reify-traits [simple-cached-node simple-watched or-summarizable
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

(defn- choose-leaf [verified-summary]
 ;  (println "VS"  verified-summary)  (def *sum* verified-summary)  (Thread/sleep 10)
  (->> (summary/extract-leaf-seq verified-summary (comp empty? summary/children))
       (map summary/source)
       (filter can-evaluate?)
       #_ first  last #_  rand-nth))

(defn- solve [root-subproblem]
  (def *root* root-subproblem)
  (summary/solve
   #(summaries/verified-summary (tree-summarizer root-subproblem) summary/+worst-simple-summary+)
   #(evaluate! (choose-leaf %))
   #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n))))

(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (get-atomic-stub nil inp-set fs)
        ret       (atom nil)]
    (add-watcher! root-stub (fn [root] (reset! ret root)))
    (evaluate! root-stub)
    (evaluate! root-stub)
    (assert @ret)
    @ret))


(defn implicit-fah-a*-eval2 [henv]
  (binding [*decompose-cache* (when *decompose-cache* (HashMap.))]
   (->> (fs/make-init-pair henv)
        (apply get-root-subproblem)
        solve)))

; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.fah-astar-eval2 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (do (def s summaries/summarize) (def sc summary/children) (def nc summaries/node-ordinary-children) (def src summary/source))
;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)) )))









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











(comment
 ;; This business seems to make little to no difference in pracitce, at least on
 ;; dm 1 object 3.
 ;; TODO: separate updates into user? 
 (def *nodes-to-update* (ArrayList.))

 (defn schedule-summary-change! [n]
   (.add ^ArrayList *nodes-to-update* n))

 (defn process-summary-changes! []
   (doseq [n *nodes-to-update*]
     (summaries/summary-changed! n))
   (.clear ^ArrayList *nodes-to-update*))

 (do
   (defn schedule-summary-change! [n] (summaries/summary-changed! n))
   (defn process-summary-changes! [])))



(comment
 (defn- make-nt-pair-subproblem [subsuming-sp pair-stub left-sp right-sp]
   (let [ret (make-simple-subproblem
              pair-stub subsuming-sp (output-set right-sp) false             
              or-summary
              (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                                          (subproblem-name right-sp) #(refine-input right-sp %)))
              0)
         [ss watch stub-f]
         (if (terminal? left-sp)        ;Expand right?
           [(make-sum-summarizer [(tree-summarizer left-sp) right-sp])
            right-sp #(make-pair-stub2 nil left-sp (stub %))]
           [(make-sum-summarizer [left-sp (tree-summarizer right-sp)])
            left-sp #(make-pair-stub2 nil % (refine-input right-sp (output-set %)))])]

     (summaries/connect! ret ss false)
    
     (add-watcher! watch
                   (fn [o]
                     (summaries/summary-changed-local! ss)
                     (connect-and-watch! ret (stub-f o) #(add-sp-child! ret %))
                     (summaries/summary-changed! ret))) ;; TODO: efficiency?
    
     ret))

 (defn- make-pair-subproblem [subsuming-sp pair-stub left-sp right-sp]
   (if (and (terminal? left-sp) (terminal? right-sp))
     (make-simple-subproblem
      pair-stub subsuming-sp (output-set right-sp) true
      (fn [s b] (summary/+ (summaries/summary left-sp) (summaries/summary right-sp) s b))
      (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                                  (subproblem-name right-sp) #(refine-input right-sp %)))
      0)
     (make-nt-pair-subproblem subsuming-sp pair-stub left-sp right-sp))))