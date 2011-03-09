(ns angelic.search.implicit.fah-astar-eval2
  (:require [angelic.util :as util]
            [angelic.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries_old :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList]))

;; A version of eval subproblems where we explicitly represent the relationships
;; between subproblems, and allow "listeners" that wait for a subproblem to be
;; evaluated.

;; Assuming consistency and evaluation s.t. no bounding is necessary.
;; Otherwise, downwards would be better anyway?

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


(set! *warn-on-reflection* true)

;; TODO: note lazy is so lazy about subsumption , ...

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Watchers      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol OutputWatched
  (add-watcher!   [s w] "Add a watcher to be notified of all outputs to this.
                         A watcher is just a fn of [watched-sp/stub new-subproblem]."))

(defprotocol SimpleWatched
  (add-output! [sw o])
  (add-forward! [sw child-sw]))

(traits/deftrait simple-watched
  [] [^ArrayList watchers (ArrayList.)
      ^ArrayList outputs (ArrayList.)
      ^ArrayList forwards (ArrayList.)] []
  OutputWatched
  (add-watcher! [sw w]
    (.add watchers w)
    (doseq [o outputs] (w sw o))
    (doseq [f forwards] (add-watcher! f w)))
  
  SimpleWatched
  (add-output! [sw o]
;   (assert (satisfies? Subproblem o))
    (.add outputs o)
    (doseq [w watchers] (w sw o)))
  (add-forward! [sw child-sw]
    (.add forwards child-sw)
    (doseq [w watchers] (add-watcher! child-sw w))))

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
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return further outputs."))

(defprotocol Stub
  (input-set         [s])
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn refine-stub-input [s ref-inp])
;; Need ability to refine input of stub -- to allow chaining of right refinements.

(defn subproblem? [s]
  (instance? angelic.search.implicit.fah_astar_eval2.Subproblem s))

(defn sp-str [sp]
  (format "#<Subproblem$%h %s>"
          (System/identityHashCode sp) (subproblem-name sp)))
(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem
  [ss o] (print-method (sp-str ss) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expects to be a parent of inside, but not have inside as a child.
;; All children are tree summarizers.
;; Non-subsuming children must be added by calling connect-child-sp!
(defprotocol TreeSummarizer
  (connect-child-sp! [ts child-sp])
  (get-inner-sp [ts]))


(defn make-tree-summarizer [inner-sp assert-monotonic?]
 (let [last-sum (atom nil)]
  (traits/reify-traits
   [summaries/simple-node cache-trait simple-watched]

   TreeSummarizer
   (get-inner-sp [ts] inner-sp)
   (connect-child-sp! [ts child-sp]
     (summaries/connect! ts (tree-summarizer child-sp) false)
     (add-output! ts child-sp)
     (let [my-sum (summaries/summary ts)
           child-sum (summaries/summary (tree-summarizer child-sp))]
       (when assert-monotonic?
         (util/assert-is (>= (summary/max-reward my-sum) (summary/max-reward child-sum)) "%s" [:AC inner-sp]))
       (when-not (summary/>= my-sum child-sum)
         (summaries/summary-changed! ts))))
    
   summaries/Summarizable
   (summarize [s]
     (swap! summaries/*summary-count* inc)
     (let [sum (summary/or-combine
                 (cons (summaries/summary inner-sp)
                       (map summaries/summary (summaries/node-ordinary-children s)))
                 s
                 (->> (summaries/node-subsuming-children s)
                      (map (comp summary/max-reward summaries/summary))
                      (cons Double/POSITIVE_INFINITY)
                      (apply min)))]
       (when (and assert-monotonic? @last-sum)
         (util/assert-is (>= (summary/max-reward @last-sum) (summary/max-reward sum)) "%s" [:s inner-sp]))
       (reset! last-sum sum))))))



(defn ts-str [sp]
  (format  "#<TreeSummarizer$%h %s>"
           (System/identityHashCode sp) (subproblem-name (get-inner-sp sp))))
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer
  [ss o] (print-method (ts-str ss) o))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-simple-subproblem* [name stub out-set terminal? summary-fn]
  (let [ts-atom (atom nil)
        ret (traits/reify-traits [cache-trait summaries/simple-node]
             summaries/Summarizable (summarize [s] (assert (empty? (summaries/node-subsuming-children s))) (summary-fn s))
             Subproblem             (subproblem-name [s] name)
                                    (output-set       [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
                                    (terminal?       [s] terminal?)
             Stub                   (input-set       [s] (input-set stub))
                                    (refine-input    [s ni] (println "RI" (drop-last name)) (refine-input stub ni)))  
        ts  (make-tree-summarizer ret (= ::Atomic (first name)))]
    (summaries/add-parent! ret ts false)
    (reset! ts-atom ts)
    ret))

(defn make-terminal-subproblem [name subsuming-sp stub out-set reward status]
  (assert (#{:blocked :solved} status))
  (let [summary-fn #(summary/make-simple-summary reward status %)
        ret        (make-simple-subproblem* name stub out-set true summary-fn)]
    (when subsuming-sp (summaries/connect! (tree-summarizer ret) (tree-summarizer subsuming-sp) true))
    ret))

;; Children should be lazy, are not touched if subsuming criteria are met?
(defn make-nonterminal-subproblem [name subsuming-sp stub out-set summary-fn
                                   use-sub-children? inner-children copy-children child-transform]
  (let [ret (make-simple-subproblem* name stub out-set false summary-fn)]
    (when subsuming-sp (summaries/connect! (tree-summarizer ret) (tree-summarizer subsuming-sp) true))
    (if (and subsuming-sp use-sub-children? (not (terminal? subsuming-sp)))
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
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;     Subproblem Types and Stubs     ;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-fs-seq-stub make-atomic-stub)

 ;; TODO: add refine-input- to skip comparisons?
(defn- make-atomic-subproblem [stub subsuming-sp inp-set function-set out-set reward status]
  (let [name    [::Atomic (fs/fs-name function-set) inp-set]]
    (if (= status :live)
      (let [children (lazy-seq (map #(make-fs-seq-stub inp-set %)
                                    (fs/child-seqs function-set inp-set)))]
        (make-nonterminal-subproblem
         name subsuming-sp stub out-set
         (fn [s] (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s)) s reward))
         true children children (fn [_ o] o)))
      (make-terminal-subproblem name subsuming-sp stub out-set reward status))))

;; TODO: subsumption links should be to tree su, not stub ? 
;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [subsuming-stub inp-set function-set]
;  (println "Making atomic stub" inp-set (fs/fs-name function-set))
  (let [state (atom :ready) ;; set to [out-set reward] after first eval, then :go after second.
        ret
        (traits/reify-traits
         [simple-watched cache-trait (summaries/fixed-node nil)]
         summaries/Summarizable
         (summarize [s] (assert (empty? (summaries/node-subsuming-children s)))
           (cond (= :ready @state) (summary/make-live-simple-summary 0 s)
                 (= :go    @state) summary/+worst-simple-summary+
                 :else             (summary/make-live-simple-summary (second @state) s)))   
         Evaluable
         (evaluate! [s]
           (assert (not (= :go @state)))
           (let [ready?                  (= :ready @state)]
             (if-let [[out-set reward :as op] (if ready? (fs/apply-opt function-set inp-set) @state)]
               (let [status (if ready? (fs/status function-set inp-set)   :live)
                     out-fn (fn [sub] (add-output! s (make-atomic-subproblem s sub inp-set function-set
                                                                             out-set reward status)))]
                 (if (or (not ready?) (not (= status :live)))
                   (do (if subsuming-stub
                         (add-watcher! subsuming-stub (fn [_ o] (out-fn o)))
                         (out-fn nil))
                       (reset! state :go))
                   (reset! state op)))
               (reset! state :go)) ;; Kill it
             (summaries/summary-changed! s)))
         Stub
         (input-set [s] inp-set)
         (refine-input [s ni] (println "RIA" (fs/fs-name function-set) (= ni inp-set)) (if (= ni inp-set) s (make-atomic-stub s ni function-set))))]
    (when subsuming-stub (summaries/connect! ret subsuming-stub true))
    ret))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assume subsuming has same root sp1 with less refined output.
;; spse sp2 is blocked.  Then pair is terminal.
;; Have separate terminal subproblems?
;; But: why should I have to care about terminal or not ? 

;; This subproblem is allowed to die, (incl. tree?!), replaced by refinements at sp1.
;; TODO: improve refine-input function ?
;; If I have a subsuming-sp, it has child of sp2 and subsumed sp2.
(defn- make-seq-subproblem [first-stub subsuming-sp parent-sp left-sp right-sp]
  (make-nonterminal-subproblem
   [::Pair (subproblem-name left-sp) (subproblem-name right-sp)]
   subsuming-sp first-stub (output-set right-sp)   
   (fn [s] (summary/+ (summaries/summary left-sp) (summaries/summary right-sp) s))
   false [left-sp right-sp] [(tree-summarizer right-sp)]
   (fn [p o] (make-seq-subproblem first-stub nil #_ ::TODO! p left-sp o))))

;; Short circuit means that pair SP can go dead then back live.
;; TODO: right outputs use refine-input.
;; then TODO: refine-input also does structure sharing.
;; Note: right-stub may have many outputs

;; TODO: figure out how to avoid/simplify all these cases. 
(defn add-forward-child! [p c]
  (add-forward! p c)
  (summaries/connect! p c false)
  (summaries/summary-changed! p))

;; Right-stub can be a parent if parent-right? set, otherwise not.
;; Subsuming-rs is subsuming on left-sp. -- or parent  
(defn- make-rest-stub [first-stub subsuming-rs left-sp right-stub]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]  
              summaries/Summarizable
              (summarize [s] (assert (empty? (summaries/node-subsuming-children s)))
                 (summary/max
                  (summary/+ (summaries/summary left-sp) (summaries/summary right-stub) s)
                  (summary/or-combine                   
                   (map summaries/summary (summaries/node-ordinary-children s))
                   s Double/POSITIVE_INFINITY)))
              Stub
              (input-set [s] (input-set left-sp))
              (refine-input [s ri] (throw (UnsupportedOperationException.))))]
    (when subsuming-rs (summaries/connect! ret subsuming-rs true))

    (add-watcher! right-stub
      (fn [_ o]
        (add-output! ret (make-seq-subproblem first-stub nil #_ ::TODO! nil left-sp o))))
    (summaries/add-parent! left-sp ret false)
    (summaries/add-parent! right-stub ret false)

    (add-watcher! (tree-summarizer left-sp) 
      (fn [_ left-child] (println "LC!")
        (add-forward-child! ret
          (make-rest-stub first-stub ret left-child (refine-input right-stub (output-set left-child))))))
    
    ret))

;; TODO: figure out if transient increases can be solved (is there better semantics for inner)?
;; TODO: figure out how to do subsumption connections properly. 

;; Stub to wait for left to be evaluated
;; Left-stub will always be atomic stub, which always has a single output.
;; Elegant way to do parent/left barrier ? 
(defn- make-first-stub [subsuming-fs subsuming-watched left-stub right-stub-fn]
  (let [mid (atom nil)
        child-watch (traits/reify-traits [simple-watched])
        ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]
              summaries/Summarizable
              (summarize [s] (assert (empty? (summaries/node-subsuming-children s)))
                (summary/re-source 
                 (summaries/summary (or (second @mid) left-stub))
                 s Double/POSITIVE_INFINITY (if @mid :solved :live)))
              Stub
              (input-set [s] (input-set left-stub))
              (refine-input [s ri]
                (if (= ri (input-set left-stub)) s
                    (make-first-stub s child-watch (refine-input left-stub ri) right-stub-fn))))]
    (when subsuming-fs (summaries/connect! ret subsuming-fs true))
    
    (add-watcher! left-stub
      (fn [_ l]
        (assert (nil? @mid))
        (let [set-mid-fn (fn [right-sp parent-rest-stub]
                           (reset! mid [right-sp (make-rest-stub ret parent-rest-stub l right-sp)])
                           (add-output! child-watch @mid)
                           (add-forward-child! ret (second @mid)))]
          (if subsuming-fs
            (add-watcher! subsuming-watched
              (fn [_ [right-sp parent-rest-stub]]
                (set-mid-fn (refine-input right-sp (output-set l)) parent-rest-stub)))
            (set-mid-fn (right-stub-fn (output-set l)) nil)))))
 
    (summaries/connect! ret left-stub false)
    ret))


(defn- make-fs-seq-stub [inp-set [first-fs & rest-fs]]
  (let [left-stub (make-atomic-stub nil inp-set first-fs)]
    (if (empty? rest-fs)
      left-stub
      (make-first-stub nil nil left-stub #(make-fs-seq-stub % rest-fs)))))


  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- choose-leaf [verified-summary]
  (println "VS"  verified-summary) #_ (def *sum* verified-summary) (Thread/sleep 10)
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

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)))))












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
  

(defprotocol FancyNode
  (remove-child! [s child])
  (remove-parent! [s parent]))

(defn disconnect! [parent child]
  (remove-child! parent child)
  (remove-parent! child parent))


(traits/deftrait fancy-node [] [children (atom nil) parents  (atom nil)] []
  summaries/Node
  (node-ordinary-children [n] (map second (remove first @children)))
  (node-subsuming-children [n] (map second (filter first @children)))
  (node-ordinary-parents [n] (map second (remove first @parents)))
  (node-subsumed-parents [n] (map second (filter first @parents)))    
  (add-child!    [n child subsuming?] (swap! children conj [subsuming? child]))
  (add-parent!   [n parent subsuming?] (swap! parents conj [subsuming? parent]))

  FancyNode
  (remove-child! [s child]
    (let [new-children (remove #(identical? (second %) child) @children)]
      (assert (= (count new-children) (dec (count @children))))
      (reset! children new-children)))
  (remove-parent! [s parent]
    (let [new-parents (remove #(identical? (second %) parent) @parents)]
      (assert (= (count new-parents) (dec (count @parents))))
      (reset! parents new-parents))))
)


(comment
  (defn- make-atomic-subproblem [stub subsuming-sp inp-set function-set out-set reward status]
  (let [children (when (= status :live)
                   (or #_ (refined-children subsuming-as inp-set) ;; TODO!!
                       (map #(make-fs-seq-stub inp-set %)
                            (fs/child-seqs function-set inp-set))))]
    (make-simple-subproblem
     [::Atomic (fs/fs-name function-set) inp-set]
     inp-set out-set
     (if (= status :live)
       (fn [s]
         (assert (empty? (summaries/node-subsuming-children s)))
         (assert (= (count children) (count (summaries/node-ordinary-children s))))
         (summary/or-combine (map summaries/summary children) s reward))
       (fn [s] (summary/make-simple-summary reward status s)))     
     children children identity
     (fn [s ref-inp-set] (make-atomic-stub s ref-inp-set function-set))))))