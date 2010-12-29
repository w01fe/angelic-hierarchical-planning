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

;; This version has a few problems, not least multiple generation,
;; and some dangling inconsistency.
;; LAtter may be because setting of top-down-bound is not sufficient
 ;; (does not pass through tree summarizers, just goes inside).

;; Assuming consistency and evaluation s.t. no bounding is necessary.
;; Otherwise, downwards would be better anyway?
;; Note: simple implicit valuations means consistency impossible,
;; need downwards propagation ...
;; Two possibilities:
;; 1 - pass downward
;; 2 - assign,e .g., sub parent as child graduates.
;;  Inner should also take bound from tree summarizer.
;; This seems like cleanest option . 

;; Breaks down into "subproblems" with well-defined action seqs, inputs, outputs,
;; and "stubs" where output is not known yet.
;; Summary of either represents child subproblems not yet produced.
;; These are produced into "tree summary", which has semantic view.

;; One issue with this formulation is that pair-subproblems can
;; decrease and increase reward arbitrarily (with shortcutting)
;; as they get cut off by left sp, then recreated by children.

;; Taxonomy here:
;; Subproblems
;; All have tree summarizer- representing semantic view
;; And internal summary -- representing children not yet produced.
;; Atomic has internal children -- stubs of each refinement
;;  Copies outputs to its own outputs
;; Pair has internal child -- inner of right side
;;  Copies output to own outputs
;; Both can also be in "refinement" mode, where they forward to refinements of outputs.

;; Stubs -- represent partially evaluated subproblems.
;; Atomic stub is simple- evaluate once to get description, second time to get children.
;;   Children are stubs of refinements.
;; first stub is for first unevaluated subproblem
;; rest stub is for rest unevaluated subproblem.
;; Rest has one forward to pair output, another for each chld of first SP.

;; Every stub eventaully produces zero or more subproblems as output.
;;  (either directly, or through forwards to other stubs).

;; In general, to refine a subproblem we should refine its children.

;; Problems were -- refining input can produce subproblem or stub
;; Easiest if it always produces a stub.
;; Why do we have to refine stubs, though ? 

;; Came from need to chain right refinements .. ?
;; I.e., right subproblem stub can have any number of output subproblems.
;; But to do this, we just need to relax requirement that right be a stub
;; -- it just needs to be a watcher.

(set! *warn-on-reflection* true)

;; TODO: note lazy is so lazy about subsumption , ...

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)

;; TODO: right now we over-generate when we refine a pair SP; it should only consider
;; direct refinements of first SP, although this ruins...

;; TODO: why does top have so many outputs ??  Add get methods to simple-watched to debug.

;; TODO: still inconsistencies. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Watched
  (add-watcher! [s w] "Add a watcher to be notified of all outputs to this.
                         A watcher is just a fn of [watched-sp/stub new-subproblem].")
  (add-output!  [sw o]    "O is a subproblem")
  (add-forward! [sw child-sw] "child-sw is a simple-watched"))

(traits/deftrait simple-watched
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)
   ^ArrayList forwards (ArrayList.)]
  []
  Watched
  (add-watcher! [sw w]
    (.add watchers w)
    (doseq [o outputs] (w sw o))
    (doseq [f forwards] (add-watcher! f w)))
  (add-output! [sw o]
    (.add outputs o)
    (doseq [w watchers] (w sw o)))
  (add-forward! [sw child-sw]
    (.add forwards child-sw)
    (doseq [w watchers] (add-watcher! child-sw w))))


;; Note: this entails zero minimum cost (i.e., nonnegative costs).
(defn subsuming-bound [s]
  (->> (summaries/node-subsuming-children s)
       (map (comp summary/max-reward summaries/summary))
       (apply min 0)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Protocols     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Evaluable
  (evaluate!      [s]))

(defn can-evaluate? [s]
  (instance? angelic.search.implicit.fah_astar_eval2.Evaluable s))

(defprotocol Subproblem
  (subproblem-name   [s])
  (input-set         [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return further outputs.")
  (refine-input      [s refined-input-set] "Return a child stub.")

  (top-down-bound    [s])
  (add-top-down-bound! [s b]))


(defn sp-str [sp]
  (format "#<Subproblem$%h %s>" (System/identityHashCode sp) (subproblem-name sp)))
(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem
  [ss o] (print-method (sp-str ss) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expects to be a parent of inside, but not have inside as a child.
;; All children are tree summarizers.
;; Non-subsuming children must be added by calling connect-child-sp!
(defprotocol TreeSummarizer
  (connect-child-sp! [ts child-sp])
  (get-inner-sp      [ts] "Get subproblem for this ts"))

;; TODO: lots of negative-infinities showing up in ordinary children -- remove them.
;; (pairs gone empty ? )

(defn make-tree-summarizer [inner-sp assert-monotonic?]
 (let [last-sum (atom nil)]
  (traits/reify-traits
   [summaries/simple-node cache-trait simple-watched]

   TreeSummarizer
   (get-inner-sp [ts] inner-sp)
   (connect-child-sp! [ts child-sp]
     (summaries/connect! ts (tree-summarizer child-sp) false)
     (add-top-down-bound! child-sp (top-down-bound inner-sp))
     (add-output! ts child-sp)
     (let [my-sum (summaries/summary ts)
           child-sum (summaries/summary (tree-summarizer child-sp))]
       (when assert-monotonic?
         (util/assert-is (>= (summary/max-reward my-sum) (summary/max-reward child-sum)) "%s" [:AC (def *sum* ts) (def *child-sp* child-sp) inner-sp (subsuming-bound ts)]))
       (when-not (summary/>= my-sum child-sum) ;         (println "New child inc" my-sum child-sum ts child-sp)
         (summaries/summary-changed! ts))))
    
   summaries/Summarizable
   (summarize [s]
     (swap! summaries/*summary-count* inc)
     (let [sum (summary/or-combine
                 (cons (summaries/summary inner-sp)
                       (map summaries/summary (summaries/node-ordinary-children s)))
                 s (subsuming-bound s))]
       (when (and assert-monotonic? @last-sum)
       (util/assert-is (>= (summary/max-reward @last-sum) (summary/max-reward sum)) "%s" [:s (def *sum* s) inner-sp]))
       (reset! last-sum sum))))))



(defn ts-str [sp]
  (format  "#<TreeSummarizer$%h %s>"
           (System/identityHashCode sp) (subproblem-name (get-inner-sp sp))))
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer
  [ss o] (print-method (ts-str ss) o))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add bounds -- needed because of simple valuation stuff -- even with consistency.

(defn make-single-output-stub [out-sp]
  (let [ret (traits/reify-traits [cache-trait summaries/simple-node simple-watched]
              summaries/Summarizable (summarize [s] summary/+worst-simple-summary+))]
    (add-output! ret out-sp)
    ret))

(defn make-simple-subproblem* [name inp-set out-set terminal? summary-fn ri-fn]
  (let [ts-atom (atom nil)
        tdb-atom (atom 0) ;; TODO: factor out into trait?
        ret (traits/reify-traits [cache-trait summaries/simple-node]
             summaries/Summarizable (summarize       [s] (summary-fn s @tdb-atom))
             Subproblem             (subproblem-name [s] name)
                                    (input-set       [s] inp-set)
                                    (output-set      [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
                                    (terminal?       [s] terminal?)
                                    (refine-input    [s ni]
                                      (if (= ni inp-set) (make-single-output-stub s) (ri-fn s ni)))
                                    (top-down-bound [s] @tdb-atom)
                                    (add-top-down-bound! [s b]
                                      (when (< b @tdb-atom)
                                        (reset! tdb-atom b)
                                        (summaries/summary-changed! s))))        
        ts  (make-tree-summarizer ret (= ::Atomic (first name)))]
    (summaries/add-parent! ret ts false)
    (reset! ts-atom ts)
    ret))

(defn make-terminal-subproblem [name subsuming-sp inp-set out-set reward status ri-fn]
  (assert (#{:blocked :solved} status))
  (let [summary-fn (fn [s b] (summary/make-simple-summary (min b reward) status s))
        ret        (make-simple-subproblem* name inp-set out-set true summary-fn ri-fn)]
    (when subsuming-sp (summaries/connect! (tree-summarizer ret) (tree-summarizer subsuming-sp) true))
    ret))

;; Children should be lazy, are not touched if subsuming criteria are met?
(defn make-nonterminal-subproblem [name subsuming-sp inp-set out-set summary-fn init-bound ri-fn
                                   use-sub-children? inner-children copy-children child-transform]
  (let [sub-children? (and subsuming-sp use-sub-children? (not (terminal? subsuming-sp)))
        ret (make-simple-subproblem* name inp-set out-set false
                                     (if sub-children?
                                       (fn [s b]
                                         (summary/max (summary-fn s b)
                                           (summary/re-source (summaries/summary subsuming-sp) s b :solved)))
                                       summary-fn)
                                     ri-fn)]
    (when subsuming-sp (summaries/connect! (tree-summarizer ret) (tree-summarizer subsuming-sp) true))
    (when sub-children? (summaries/connect! ret subsuming-sp false))
    (if sub-children?
      (add-watcher! (tree-summarizer subsuming-sp)
        (fn [_ sub-out]
          (let [sub-stub (refine-input sub-out (input-set ret))]
            (summaries/connect! ret sub-stub false)
            (add-watcher! sub-stub
              (fn [_ out-sp] (connect-child-sp! (tree-summarizer ret) out-sp))))))
      (do (doseq [child inner-children]
            (summaries/connect! ret child false))
          (doseq [child copy-children]
            (add-watcher! child
                          (fn [_ out-sp] (connect-child-sp! (tree-summarizer ret) (child-transform ret out-sp)))))))
    (add-top-down-bound! ret init-bound)
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;     Subproblem Types and Stubs     ;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-fs-seq-stub make-atomic-stub)

;; TODO: pass reward through so it propagates through outputs.
;; How to do this elegantly ? 
(defn- make-atomic-subproblem [stub subsuming-sp inp-set function-set out-set reward status]
  (let [name [::Atomic (fs/fs-name function-set) #_ inp-set]
        ri-fn    (fn [s ri] (make-atomic-stub s ri function-set))]
    (if (= status :live)
      (let [children (lazy-seq (map #(make-fs-seq-stub inp-set %)
                                    (fs/child-seqs function-set inp-set)))]
        (make-nonterminal-subproblem
         name subsuming-sp inp-set out-set
         (fn [s b] (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s)) s b)) reward
         ri-fn true children children (fn [_ o] o)))
      (make-terminal-subproblem name subsuming-sp inp-set out-set reward status ri-fn))))

(defn connect-subsuming! [child subsuming-sp]
  (when subsuming-sp (summaries/connect! child (tree-summarizer subsuming-sp) true)))


;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [subsuming-sp inp-set function-set]
  (let [state (atom :ready) ;; set to [out-set reward] after first eval, then :go after second.
        ret
        (traits/reify-traits
         [simple-watched cache-trait (summaries/fixed-node nil)]
         summaries/Summarizable
         (summarize [s]
;                    (println (subsuming-bound s) (fs/fs-name function-set))         
           (cond (= :ready @state) (summary/make-live-simple-summary (subsuming-bound s) s)
                 (= :go    @state) summary/+worst-simple-summary+
                 :else             (summary/make-live-simple-summary (second @state) s)))   
         Evaluable
         (evaluate! [s]
           (assert (not (= :go @state)))
           (let [ready?                  (= :ready @state)]
             (if-let [[out-set reward :as op] (if ready? (fs/apply-opt function-set inp-set) @state)]
               (let [status (if ready? (fs/status function-set inp-set)   :live)]
                 (if (or (not ready?) (not (= status :live)))
                   (do (add-output! s (make-atomic-subproblem s subsuming-sp inp-set function-set
                                                              out-set reward status))
                       (reset! state :go))
                   (reset! state op)))
               (reset! state :go)) ;; Kill it
             (summaries/summary-changed! s))))]
    (connect-subsuming! ret subsuming-sp)
    ret))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-first-stub)
;; This subproblem is allowed to die, (incl. tree?!), replaced by refinements at sp1.
;; TODO: improve refine-input function ?
;; TODO: parent sp.
;; TODO: refine-input function is multiple generating, since children of left-sp go twice.
;; If I have a subsuming-sp, it has child of sp2 and subsumed sp2.
(defn- make-seq-subproblem [subsuming-sp parent-sp left-sp right-sp]
  (make-nonterminal-subproblem
   [::Pair (subproblem-name left-sp) (subproblem-name right-sp)]
   subsuming-sp (input-set left-sp) (output-set right-sp)   
   (fn [s b] (summary/+ (summaries/summary left-sp) (summaries/summary right-sp) s b)) 0
   (fn [s ri] (make-first-stub s (refine-input left-sp ri) #(refine-input right-sp %)))
   false [left-sp right-sp] [(tree-summarizer right-sp)]
   (fn [p o] (make-seq-subproblem nil #_ ::TODO! p left-sp o))))

;; Short circuit means that pair SP can go dead then back live.
;; TODO: right outputs use refine-input.
;; then TODO: refine-input also does structure sharing.
;; Note: right-stub may have many outputs

;; TODO: figure out how to avoid/simplify all these cases. 
(defn add-forward-child! [p c]
  (println "AFC" p c)
  (add-forward! p c)
  (summaries/connect! p c false)
  (summaries/summary-changed! p))

(defn- make-input-wrapped-stub [stub new-input]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]  
              summaries/Summarizable
              (summarize [s] (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s))
                                                 s Double/POSITIVE_INFINITY)))]
    (summaries/connect! ret stub false)
    (add-watcher! stub (fn [_ o] (add-forward-child! ret (refine-input o new-input))))
    ret))

;; Right-stub can be a parent if parent-right? set, otherwise not.
;; Subsuming-rs is subsuming on left-sp. -- or parent
(defn- make-rest-stub [subsuming-sp left-sp right-stub]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]  
              summaries/Summarizable
              (summarize [s] 
                (let [b (subsuming-bound s)]
                  (summary/max ;; Max here prevents infinite loop from s in s
                   (summary/+ (summaries/summary left-sp) (summaries/summary right-stub) s b)
                   (summary/or-combine                   
                    (map summaries/summary (summaries/node-ordinary-children s))
                    s b)))))]
    (connect-subsuming! ret subsuming-sp)

    (add-watcher! right-stub
      (fn [_ o]
        (add-output! ret (make-seq-subproblem subsuming-sp nil #_ ::?? left-sp o))))
    (summaries/add-parent! left-sp ret false)
    (summaries/add-parent! right-stub ret false)

    (add-watcher! (tree-summarizer left-sp) 
      (fn [_ left-child] 
        (add-forward-child! ret 
          (make-rest-stub subsuming-sp left-child
                          (make-input-wrapped-stub right-stub (output-set left-child))))))
    
    ret))

;; TODO: figure out if transient increases can be solved (is there better semantics for inner)?
;; Stub to wait for left to be evaluated
;; Left-stub will always be atomic stub, which always has a single output.
;; TODO: this seems to not always be true -- someitmes get multiple outputs for left-stub !
;; In particular, left-stub can be refined-input of child of atomic ?!
;; Should not be a problem with top-down refinement ...
(defn- make-first-stub [subsuming-sp left-stub right-stub-fn]
  (let [mid (atom nil)
        ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]
              summaries/Summarizable
              (summarize [s] 
                (summary/re-source 
                 (summaries/summary (or @mid left-stub))
                 s (subsuming-bound s) (if @mid :solved :live))))]
    (connect-subsuming! ret subsuming-sp)
    
    (add-watcher! left-stub
      (fn [_ l]
        (assert (nil? @mid))
        (reset! mid (make-rest-stub subsuming-sp l (right-stub-fn (output-set l))))
        (add-forward-child! ret @mid)))
    (summaries/connect! ret left-stub false)

    ret))


(defn- make-fs-seq-stub [inp-set [first-fs & rest-fs]]
  (let [left-stub (make-atomic-stub nil inp-set first-fs)]
    (if (empty? rest-fs)
      left-stub
      (make-first-stub nil left-stub #(make-fs-seq-stub % rest-fs)))))


  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- choose-leaf [verified-summary]
  (println "VS"  verified-summary)  (def *sum* verified-summary) (Thread/sleep 10)
  (->> (summary/extract-leaf-seq verified-summary (comp empty? summary/children))
;       util/prln
;       (#(do (def *bads* %) %))
       (map summary/source)
;       util/prln
;       (#(do (def *bad* %) %))
       (filter can-evaluate?)
       last #_ rand-nth))

(defn- solve [root-subproblem]
  (def *root* root-subproblem)
  (summary/solve
   #(summaries/verified-summary (tree-summarizer root-subproblem) summary/+worst-simple-summary+)
   (comp evaluate! choose-leaf)
   #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n))))

(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil inp-set fs)
        ret       (atom nil)]
    (add-watcher! root-stub (fn [_ root] (reset! ret root)))
    (evaluate! root-stub)
    (evaluate! root-stub)
;    (println root-stub (summaries/summary root-stub) ret)
    (assert @ret)
    @ret))


(defn implicit-fah-a*-eval2 [henv]
  (->> (fs/make-init-pair henv)
       (apply get-root-subproblem)
       solve))

; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.fah-astar-eval2 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

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

