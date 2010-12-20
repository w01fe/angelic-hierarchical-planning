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

;; Assuming consistency and evaluation s.t. no bounding is necessary.
;; Otherwise, downwards would be better anyway?

;; Breaks down into "subproblems" with well-defined action seqs, inputs, outputs,
;; and "stubs" where output is not known yet.
;; Summary of either represents child subproblems not yet produced.
;; These are produced into "tree summary", which has semantic view.

;; One issue with this formulation is that pair-subproblems can
;; decrease and increase reward arbitrarily (with shortcutting)
;; as they get cut off by left sp, then recreated by children.

(set! *warn-on-reflection* true)


#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
 (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
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

(defn can-evaluate? [s]  (instance? angelic.search.implicit.fah_astar_eval2.Evaluable s))

(defprotocol Subproblem
  (subproblem-name   [s])
  (input-set         [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (refine-input      [s refined-input-set] "Return a child stub that refines the input of s."))


(defn sp-str [sp] (format  "#<Subproblem$%h %s>" (System/identityHashCode sp) (subproblem-name sp)) )
(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem [ss o] (print-method (sp-str ss) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     (summaries/connect! ts (tree-summarizer child-sp) false)
     (add-output! ts child-sp)
     (let [my-sum (summaries/summary ts) child-sum (summaries/summary (tree-summarizer child-sp))]
;       (util/assert-is (>= (summary/max-reward my-sum) (summary/max-reward child-sum)))  Cannot assert this -- see above.
       (when-not (summary/>= my-sum child-sum)
         (summaries/summary-changed! ts))))
    
   summaries/Summarizable
   (summarize [s]
     (swap! summaries/*summary-count* inc)
     (summary/or-combine
      (cons (summaries/summary inner-sp) (map summaries/summary (summaries/node-ordinary-children s)))
      s
      (summary/max-reward (apply summary/min (map summaries/summary (summaries/node-subsuming-children s))))))))



(defn ts-str [sp] (format  "#<TreeSummarizer$%h %s>" (System/identityHashCode sp) (subproblem-name (get-inner-sp sp))) )
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer [ss o] (print-method (ts-str ss) o))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-simple-subproblem [name inp-set out-set summary-fn refine-input-fn]
  (let [ts-atom (atom nil)
        ret (traits/reify-traits [cache-trait summaries/simple-node]
             summaries/Summarizable (summarize [s] (summary-fn s))
             Subproblem             (subproblem-name [s] name)
                                    (input-set       [s] inp-set)
                                    (output-set       [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
                                    (refine-input    [s new-inp-set]
                                     (if (= inp-set new-inp-set) s (refine-input-fn s new-inp-set))))        
        ts  (make-tree-summarizer ret)]
    (summaries/add-parent! ret ts false)
    (reset! ts-atom ts)
    ret))

(defn setup-ordinary-subproblem! [sp inner-children copy-children child-transform]
  (doseq [child inner-children]
    (summaries/connect! sp child false))
  (doseq [child copy-children]
    (add-watcher! child (fn [_ out-sp] (connect-child-sp! (tree-summarizer sp) (child-transform out-sp))))))

(defn setup-subsumed-subproblem! [sp subsuming-sp]
  (summaries/connect! (tree-summarizer sp) (tree-summarizer subsuming-sp) true)
  (add-watcher! subsuming-sp
     (fn [_ sub-out]
       (let [sub-stub (refine-input sub-out (input-set sp))]
         (summaries/connect! sp sub-stub)
         (add-watcher! sub-stub
           (fn [_ out-sp] (connect-child-sp! (tree-summarizer sp) out-sp)))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;     Subproblem Types and Stubs     ;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-fs-seq-stub make-atomic-stub)

 ;; TODO: add refine-input- to skip comparisons?
(defn- make-atomic-subproblem [stub subsuming-sp subsuming-children? inp-set function-set out-set reward status]
  (let [sp (make-simple-subproblem
            [::Atomic (fs/fs-name function-set) inp-set]
            inp-set out-set
            (if (= status :live)
              (fn [s] (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s)) s reward))
              (fn [s] (summary/make-simple-summary reward status s)))
            (fn [s inp] (make-atomic-stub s (= status :live) inp function-set)))]
    (when (= status :live)
      (when subsuming-sp (setup-subsumed-subproblem! sp subsuming-sp))
      (when-not subsuming-children?
        (let [children (map #(make-fs-seq-stub inp-set %) (fs/child-seqs function-set inp-set))]
          (setup-ordinary-subproblem! sp children children identity))))
    sp))


;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [subsuming-sp subsuming-children? inp-set function-set]
;  (println "Making atomic stub" inp-set (fs/fs-name function-set))
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
               (do (add-output! s (make-atomic-subproblem s subsuming-sp subsuming-children?
                                                          inp-set function-set out-set reward status))
                   (reset! state :go))
               (reset! state op)))
           (reset! state :go)) ;; Kill it
         (summaries/summary-changed! s))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This subproblem is allowed to die, (incl. tree?!), replaced by refinements at sp1. 
(defn- make-pair-subproblem [stub sp1 sp2]
  (doto (make-simple-subproblem
         [::Pair (subproblem-name sp1) (subproblem-name sp2)]
         (input-set sp1) (output-set sp2)
         (fn [s] (summary/+ (summaries/summary sp1) (summaries/summary sp2) s))
         (fn [s inp] nil))    
    (setup-ordinary-subproblem! [sp1 sp2] [(tree-summarizer sp2)] (fn [s] (make-pair-subproblem stub sp1 s)))))

;; Short circuit means that right SP can go dead then back live. 
(defn- make-right-stub [left-sp right-stub right-stub-fn]
  (let [ret (traits/reify-traits [simple-watched cache-trait summaries/simple-node]  
              summaries/Summarizable
              (summarize [s]
                 (summary/max
                  (summary/+ (summaries/summary left-sp) (summaries/summary right-stub) s)
                  (summary/or-combine                   
                   (map summaries/summary (summaries/node-ordinary-children s))
                   s Double/POSITIVE_INFINITY))))]
    (add-watcher! right-stub (fn [_ o] (add-output! ret (make-pair-subproblem ret left-sp o))))
    (summaries/add-parent! left-sp ret false)
    (summaries/add-parent! right-stub ret false)

    ;; Note: this right-sharing is crucial for efficiency!     
    (add-watcher! (tree-summarizer left-sp) 
      (fn [_ left-child]
        (let [right-right (if (= (output-set left-child) (output-set left-sp)) right-stub (right-stub-fn (output-set left-child)))
              new-right-stub (make-right-stub left-child right-right right-stub-fn)]
          (summaries/connect! ret new-right-stub false)
          (add-forward! ret new-right-stub)
          (summaries/summary-changed! ret))))
    
    ret))


;; Stub to wait for left to be evaluated
;; Left-stub will always be atomic stub, which always has a single output.
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
        (reset! mid (make-right-stub l (right-stub-fn (output-set l)) right-stub-fn))
        (add-forward! ret @mid)
        (summaries/connect! ret @mid false)
        (summaries/summary-changed! ret)))    
    (summaries/connect! ret left-stub false)
    ret))


(defn- make-fs-seq-stub [inp-set [first-fs & rest-fs]]
  (let [first-stub (make-atomic-stub nil false inp-set first-fs)]
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

(defn- choose-leaf [verified-summary]
;  (println "VS"  verified-summary) #_ (def *sum* verified-summary) (Thread/sleep 10)
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
  (let [root-stub (make-atomic-stub nil false inp-set fs)
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