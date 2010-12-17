(ns angelic.search.implicit.fah-astar-eval2
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap]))

;; A version of eval subproblems where we explicitly represent the relationships
;; between subproblems, and allow "listeners" that wait for a subproblem to be
;; evaluated.
;; Subproblems where the expand operation evaluates the output set, and generates
;; the children.  Putting the focus on evaluation gives us finer granularity,
;; allowing full utilizatino of subsumption, plus is more natural in a decomposed
;; setting where we also have to "evaluate" existing actions in new contexts.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A subproblem should also implement Summarizable and Refinable implementations.
;; The non-viable (pre-refinement) subproblem is always represented as nil.

;; Here, get-child and refine-input always return subproblems,
;; but output-set can return "nil"
;; get-child and refine-input are allow to return nil


(defprotocol OutputWatched
  (add-watcher!   [s w] "Add a watcher to be notified of all outputs to this.
                         A watcher is just a fn of [watched-sp/stub new-subproblem]."))

(defprotocol Evaluable
  (evaluate!      [s]))

(defn can-evaluate? [s]
  (satisfies? Evaluable s))

;; Subproblem must also implement SubproblemStub.
(defprotocol Subproblem
  (subproblem-name   [s])
  (input-set         [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children."))


(comment ; TODO: refine-input must go somewhere
  (refine-input      [s maybe-refined-input-set])  
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))


(defn sp-str [sp] (format  "#<Subproblem$%h %s>" (System/identityHashCode sp) (subproblem-name sp)) )
(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem [ss o] (print-method (sp-str ss) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)


(defprotocol SimpleWatched
  (add-output! [sw o])
  (add-forward! [sw child-sw]))

(traits/deftrait simple-watched
  [] [watchers (atom nil) outputs (atom nil) forwards (atom nil)] []
  OutputWatched
  (add-watcher! [sw w]
    (swap! watchers conj w)
    (doseq [o @outputs] (w sw o))
    (doseq [f @forwards] (add-watcher! f w)))
  
  SimpleWatched
  (add-output! [sw o]
    (assert (satisfies? Subproblem o))
    (swap! outputs conj o)
    (doseq [w @watchers] (w sw o)))
  (add-forward! [sw child-sw]
    (swap! forwards conj child-sw)
    (doseq [w @watchers] (add-watcher! child-sw w))))



;; Expects to be a parent of inside, but not have inside as a child.
;; All children are tree summarizers.
;; Non-subsuming children must be added by calling connect-child-sp!
(defprotocol TreeSummarizer
  (connect-child-sp! [ts child-sp])
  (get-inner-sp [ts]))


(defn make-tree-summarizer [inner-sp]
  (traits/reify-traits
   [summaries/simple-node cache-trait simple-watched]

   TreeSummarizer
   (get-inner-sp [ts] inner-sp)
   (connect-child-sp! [ts child-sp]
;                      (println "CC" inner-sp child-sp)
     (summaries/connect! ts (tree-summarizer child-sp) false)
     (add-output! ts child-sp)
     (add-forward! ts child-sp)
     (summaries/summary-changed! ts))
    
   summaries/Summarizable
   (summarize [s]
     (swap! summaries/*summary-count* inc)
     ;;    (util/print-debug 5 "refresh-outer" inside (summaries/summary inside) (summaries/node-ordinary-children s))
     (summary/or-combine
      (cons (summaries/summary inner-sp) (map summaries/summary (summaries/node-ordinary-children s)))
      s
      (summary/max-reward (apply summary/min (map summaries/summary (summaries/node-subsuming-children s))))))))

(defn ts-str [sp] (format  "#<TreeSummarizer$%h %s>" (System/identityHashCode sp) (subproblem-name (get-inner-sp sp))) )
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer [ss o] (print-method (ts-str ss) o))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Traits ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(comment (defn tree-summary [sp] (summaries/summary (tree-summarizer sp))))

(comment
 (defn persistent-watcher [w]
   (fn p-watch [watched child]
     (add-watcher! (tree-summarizer child) p-watch)
     (w watched child))))


(defn make-simple-subproblem [name inp-set out-set summary-fn inner-children copy-children child-transform]
  (let [ts-atom (atom nil)
        ret (traits/reify-traits [cache-trait summaries/simple-node]
             summaries/Summarizable (summarize [s] (summary-fn s))
             Subproblem             (subproblem-name [s] name)
                                    (input-set       [s] inp-set)
                                    (output-set       [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
             OutputWatched          (add-watcher! [s w] (add-watcher! @ts-atom w)))
        ts  (make-tree-summarizer ret)]
    ;; Set up tree summarizer
    (summaries/add-parent! ret ts false)
    (reset! ts-atom ts)

    ;; Set up summary children
    (doseq [child inner-children]
      (summaries/connect! ret child false))

    ;; Set up watching for outputs of children, to copy to self.
    (doseq [child copy-children]
      (add-watcher! child (fn [_ out-sp] #_(println "TTT" out-sp) (connect-child-sp! ts (child-transform out-sp)))))

    ret))



(comment
     (refine-input    [s maybe-refined-input-set]
      (if (= input-set maybe-refined-input-set)
        s
        (let [refined (refine-input- s maybe-refined-input-set)]
          (assert refined)
          (summaries/connect! (tree-summarizer s) (tree-summarizer refined) true)
          refined))))


;;(defn get-subproblem ??)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implicit FAH A* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: "guarding" by supers

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Atomic Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-fs-seq-stub)

(comment
 (defn- refined-children [sub-sp inp-set]
   (when-let [sub-children (and sub-sp
                                (not (= :blocked (summary/status (summaries/summary sub-sp))))
                                (concat (summaries/node-ordinary-children sub-sp)
                                        (summaries/node-ordinary-children (tree-summarizer sub-sp))))]
     (map #(refine-input- % inp-set) sub-children))))


;; TODO: is leaving blocked alive the right thing ?
;; TODO: assuming consistency and evaluation s.t. no bounding is necessary. Otherwise, downwards would be better anyway?
;; TODO: do something with stub, refine-input.
(defn- make-atomic-subproblem [stub inp-set function-set out-set reward status]
;  (println (fs/fs-name function-set) inp-set)
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
     children children identity #_ #(util/prog1 % (println "AS")))))


(comment  (refine-input- [s refined-input-set]
                   (make-simple-atomic-subproblem s refined-input-set function-set)))

;; Needs a watched, with full subproblem cache, tied to output.
;; Summary should initially be 0 :live, then worst after eval.
(defn- make-atomic-stub [subsuming-as inp-set function-set]
;  (println "Making stub " inp-set (fs/fs-name function-set))
  (let [state (atom :ready)] ;; set to [out-set reward] after first eval, then :go after second.
    (traits/reify-traits [simple-watched cache-trait (summaries/fixed-node nil)]
     summaries/Summarizable
     (summarize [s]
       (cond (= :ready @state) (summary/make-live-simple-summary 0 s)
             (= :go    @state) summary/+worst-simple-summary+
             :else             (summary/make-live-simple-summary (second @state) s)))   
     Evaluable
     (evaluate! [s]
       (assert (not (= :go @state)))
       (let [ready?                  (= :ready @state)]
         (if-let [[out-set reward :as op] (if ready? (fs/apply-opt function-set inp-set) @state)]
           (let [status (if ready? (fs/status function-set inp-set)   :live)]
             (if (or (not ready?) (not (= status :live)))
               (do (add-output! s (make-atomic-subproblem s inp-set function-set out-set reward status))
                   (reset! state :go))
               (reset! state op)))
           (reset! state :go)) ;; Kill it
         (summaries/summary-changed! s))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Seq Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO TODO: think about who connects to who'se tree.
;; TODO: increase is OK as long as tree doesn't ? 

;; TODO: do something with subsuming, parent, stub, refine-input.
(defn- make-right-subproblem [stub sp1 sp2]
  (make-simple-subproblem
   [::Pair (subproblem-name sp1) (subproblem-name sp2)]
   (input-set sp1) (output-set sp2)
   (fn [s]
     (assert (empty? (summaries/node-subsuming-children s)))
     (assert (= 2 (count (summaries/node-ordinary-children s))))
     (summary/+ (summaries/summary sp1) (summaries/summary sp2) s))
   [sp1 sp2] [sp2]
   (fn [s] (make-right-subproblem stub sp1 s))))


;; Right stub should only ever has one watcher -- left stub.
(defn- make-right-stub [left-sp right-stub]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]  
              summaries/Summarizable
              (summarize [s] (summary/+ (summaries/summary left-sp) (summaries/summary right-stub) s)))]
    (add-watcher! right-stub (fn [_ o] (add-output! ret (make-right-subproblem ret left-sp o))))
    (summaries/connect! ret left-sp false)
    (summaries/connect! ret right-stub false)    
    ret))


;; TODO: should hold refined outputs until right is evaluated.
;; Basic idea: this is only thing watching sp1's output.
(defn- make-middle-stub [left-sp right-stub-fn]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]
              summaries/Summarizable
              (summarize [s]
                (summary/or-combine
                 (map summaries/summary (summaries/node-ordinary-children s))
                 s Double/POSITIVE_INFINITY)))
        add! (fn [c] (summaries/connect! ret c false) (add-forward! ret c) (summaries/summary-changed! ret))]
    (add! (make-right-stub left-sp (right-stub-fn (output-set left-sp))))
    (add-watcher! left-sp 
      (fn [_ left-child]
        (add! (make-middle-stub left-child right-stub-fn))))
    ret))


;; Stub to wait for left to be evaluated
(defn- make-left-stub [left-stub right-stub-fn]
  (let [mid (atom nil) 
        ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]
              summaries/Summarizable
              (summarize [s]
                (summary/re-source 
                 (summaries/summary (or @mid left-stub))
                 s
                 Double/POSITIVE_INFINITY
                 (if @mid :solved :live))))]
    (add-watcher! left-stub
      (fn [_ l]
        (assert (nil? @mid))
        (reset! mid (make-middle-stub l right-stub-fn))
        (add-forward! ret @mid)
        (summaries/connect! ret @mid false)
        (summaries/summary-changed! ret)))    
    (summaries/connect! ret left-stub false)
    ret))


(defn- make-fs-seq-stub [inp-set [first-fs & rest-fs]]
  (let [first-stub (make-atomic-stub nil inp-set first-fs)]
    (if (empty? rest-fs)
      first-stub
      (make-left-stub first-stub #(make-fs-seq-stub % rest-fs)))))


(comment
  (refine-input- [s refined-input-set] ;; TODO: ???
                 (make-left-pair-subproblem s nil (refine-input sp1 refined-input-set)
                                            #(refine-input (force sp2) %))))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn choose-leaf [verified-summary]
  (println verified-summary) (def *sum* verified-summary) (Thread/sleep 10)
  (->> (summary/extract-leaf-seq verified-summary (comp empty? summary/children))
       util/prln
       (#(do (def *bads* %) %))
       (map summary/source)
;       util/prln
;       (#(do (def *bad* %) %))
       (filter can-evaluate?)
       last #_ rand-nth))


(defn solve [root-subproblem]
  (def *root* root-subproblem)
  (summary/solve
   #(summaries/verified-summary (tree-summarizer root-subproblem) summary/+worst-simple-summary+)
   (comp evaluate! choose-leaf)
   #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n))))

(defn get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil inp-set fs)
        ret       (atom nil)]
    (add-watcher! root-stub (fn [_ root] (reset! ret root)))
    (evaluate! root-stub)
    (evaluate! root-stub)
    (println root-stub (summaries/summary root-stub) ret)
    (assert @ret)
    @ret))


(defn implicit-fah-a*-eval2 [henv]
  (->> (fs/make-init-pair henv)
       (apply get-root-subproblem)
       solve))














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
