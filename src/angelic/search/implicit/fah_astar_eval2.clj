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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)


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

(declare tree-summary inner-summary)

(traits/deftrait outer-or-summarizable [] [] [fancy-node cache-trait]
  summaries/Summarizable
  (summarize [s]
    (swap! summaries/*summary-count* inc)
    (summary/or-combine (map tree-summary (summaries/node-ordinary-children s)) s
                        (summary/max-reward (apply summary/min (map tree-summary (summaries/node-subsuming-children s)))))))



(traits/deftrait inner-or-summarizable [] [] [fancy-node cache-trait]
  summaries/Summarizable
  (summarize [s]
    (swap! summaries/*summary-count* inc)
    (let [inner (inner-summary s)
          bound-only? (number? inner)
          inner-bound (if bound-only? inner (summary/max-reward inner))
          bound (->> (summaries/node-subsuming-children s)
                     (map summaries/summary )
                     (apply summary/min)
                     (summary/max-reward)
                     (min inner-bound))
          child-summary (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s)) s bound)]
      (if bound-only?
        child-summary
        (summary/max child-summary inner)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A subproblem should also implement Summarizable and Refinable implementations.
;; The non-viable (pre-refinement) subproblem is always represented as nil.

;; Here, get-child and refine-input always return subproblems,
;; but output-set can return "nil"
;; get-child and refine-input are allow to return nil 

(defprotocol SubproblemWatcher
  (notify-output! [w s output-set]       "s has direct output.  (Other args?). ")
  (notify-child!  [w s child] "s has child output.  (Other args?). "))

;; Notify on child created, or evaluated ? 

(defprotocol Subproblem
  ;; External
  (subproblem-name   [s])
  (input-set         [s])
  (can-evaluate?     [s] "Is this problem evaluable and not already evaluated?")  
  (add-watcher!      [s ^SubproblemWatcher w] "Add a watcher to be notified of outputs to this, and refinements thereof.
                                   Notifies immediately if already evaluated.  Never notifies for failure.")
  (tree-summarizer   [s] "Summarizer that includes children.")
  (refine-input      [s maybe-refined-input-set])

  ;; Internal interface
  (add-child!        [s child]  "Add a child to this subproblem, and notify")
  (set-output!       [s output-set] "Set the output of this subproblem, and notify.")
  (set-sub-watched!  [s sub] "Set a subsidiary that all watchers shoudl watch as well."))

(defn tree-summary [sp] (summaries/summary (tree-summarizer sp)))

(defprotocol SubproblemImpl
  ;; External
  (evaluate!      [s] "return [output-set reward] or nil. output-pair or nil, if
                        dead / more eval needed.  Update summary to match as needed.")

  ;; Internal
  (is-evaluable?  [s] "Is this subproblem of a type that can be evaluated?")
  (inner-summary [s]  "Return summary or just numeric bound -- not including any children")
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))


;; Output-pair is [output-set init-summarizable]
(traits/deftrait simple-subproblem [name input-set]
  [output-set (atom nil) 
   watchers   (atom nil)
   tree-sum   (atom nil)
   sub-watched (atom nil)]
  [inner-or-summarizable]

  Subproblem
   (subproblem-name [s] name)
   (input-set       [s] input-set)
   (can-evaluate?   [s] (and (not @output-set) (is-evaluable? s)))
   (add-watcher! [s w]
     (swap! watchers conj w)
     (when-let [sub @sub-watched]
       (add-watcher! sub w))
     (when-let [os @output-set]
       (notify-output! w s os))
     (doseq [child (summaries/node-ordinary-children (tree-summarizer s))]
       (notify-child! w s child)))
   (tree-summarizer [s]
     (or @tree-sum
         (reset! tree-sum
           (doto (traits/reify-traits [outer-or-summarizable])
             (summaries/connect! s false)))))   
   (refine-input    [s maybe-refined-input-set]
      (if (= input-set maybe-refined-input-set)
        s
        (when-let [refined (refine-input- s maybe-refined-input-set)]
          (summaries/connect! s refined true)
          refined)))

   (add-child!      [s child]                   
     (summaries/connect! (tree-summarizer s) child false)
     (doseq [w @watchers] (notify-child! w s child)))
   (set-output!     [s o-s]
     (assert (not @output-set))
     (swap! output-set o-s)
     (doseq [w @watchers]
       (notify-output! w s o-s)))
   (set-sub-watched! [s sub]
     (assert (not @sub-watched))
     (swap! sub-watched sub)
     (doseq [w @watchers]
       (add-watcher! sub w))))


(def *subproblem-cache* (HashMap.))

;;(defn get-subproblem ??)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implicit DAH A* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: "guarding" by supers

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Atomic Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-simple-fs-seq-subproblem)

(defn- refined-children [sub-sp inp-set]
  (when-let [sub-children (and sub-sp
                               (not (= :blocked (summary/status (summaries/summary sub-sp))))
                               (concat (summaries/node-ordinary-children sub-sp)
                                       (summaries/node-ordinary-children (tree-summary sub-sp))))]
    (map #(refine-input- % inp-set) sub-children)))


(defn connect-inner-child! [sp child]
  (summaries/connect! sp child false)
  (add-watcher! child 
                (reify SubproblemWatcher
                       (notify-output! [s child output-set]
                                       (disconnect! sp child)
                                       (add-child! sp child))         
                       (notify-child! [s child grandchild] nil))))


;; TODO: is leaving blocked alive the right thing ?
;; TODO: assuming consistency and evaluation s.t. no bounding is necessary. Otherwise, downwards would be better anyway?
;; TODO: multi-step eval like earlier version?
(defn- make-simple-atomic-subproblem [subsuming-as inp-set function-set]
  (let [summary (atom nil)]
   (traits/reify-traits
    [(simple-subproblem [(fs/fs-name function-set) inp-set] inp-set)]

    SubproblemImpl
    (inner-summary [s] (or @summary (summary/make-simple-summary 0 :live s)))
    (is-evaluable? [s] true)
    (evaluate! [s]
      (if-let [[out-set reward] (fs/apply-opt function-set inp-set)]
        (let [status (fs/status function-set inp-set)]
          (reset! summary (if (= status :live) reward (summary/make-simple-summary reward status s)))
          (set-output! s out-set)
          (when (= status :live)
            (doseq [child (or (refined-children subsuming-as inp-set)
                              (map #(make-simple-fs-seq-subproblem inp-set %)
                                   (fs/child-seqs function-set inp-set)))]
              (connect-inner-child! s child))))
        (reset! summary summary/+worst-simple-summary+))
      (summaries/summary-changed! s))   
    (refine-input- [s refined-input-set]
      (make-simple-atomic-subproblem s refined-input-set function-set)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Seq Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-simple-pair-subproblem)

(defn- make-left-pair-subproblem [sub-lps parent-lps sp1 sp2-fn]
  (let [sp2-atom (atom nil) 
        ret 
        (traits/reify-traits
         [(simple-subproblem (gensym) (input-set sp1))]

         SubproblemImpl
         (inner-summary [s]
           (if-let [sp2 @sp2-atom]
             (summary/+ (tree-summary sp1) (tree-summary sp2) s)
             (summary/liven (tree-summary sp1) s)))         
         (is-evaluable? [s] false) 
         (evaluate!     [s] (throw (UnsupportedOperationException.)))
         (refine-input- [s refined-input-set] ;; TODO: fancier version?
           (assert @sp2-atom) 
           (make-left-pair-subproblem s nil (refine-input sp1 refined-input-set)
                                      #(refine-input @sp2-atom %))))]
    (add-watcher! sp1
     (reify SubproblemWatcher
            (notify-output! [w child output-set]
              (let [sp2 (sp2-fn output-set)]
                (set-sub-watched! ret sp2)
                (summaries/add-parent! sp2 ret false) ;;TODO: connect up sp2.
                (summaries/summary-changed! ret)
                (reset! sp2-atom sp2)))
            (notify-child! [w child grandchild]
              (connect-inner-child! ret (make-left-pair-subproblem nil #_ ::TODO! ret child sp2-fn)))))
    (summaries/add-parent! sp1 ret false) 
    ret))


(defn- make-right-pair-subproblem [sub-lps parent-lps sp1 sp2]
  (let [ret 
        (traits/reify-traits
         [(simple-subproblem (gensym) (input-set sp1))]

         SubproblemImpl
         (inner-summary [s] (summary/+ (tree-summary sp1) (tree-summary sp2) s))         
         (is-evaluable? [s] false)
         (evaluate!     [s] (throw (UnsupportedOperationException.)))
         (refine-input- [s refined-input-set] ;; TODO: ???
           (make-left-pair-subproblem s nil (refine-input sp1 refined-input-set)
                                        #(refine-input (force sp2) %))))]
    (add-watcher! sp2
     (reify SubproblemWatcher
            (notify-output! [w child output-set]
              (set-output! ret output-set))
            (notify-child! [w child grandchild]
              (connect-inner-child! ret make-right-pair-subproblem ::TODO?? ret sp1 child))))
    
    (summaries/add-parent! sp1 ret false)
    (summaries/add-parent! sp2 ret false)    
    ret))

(defn- make-simple-fs-seq-subproblem [inp-set [first-fs & rest-fs]]
  (let [first-sp (make-simple-atomic-subproblem nil inp-set first-fs)]
    (if (empty? rest-fs)
      first-sp
      (make-left-pair-subproblem nil nil first-sp #(make-simple-fs-seq-subproblem % rest-fs)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Driver ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At least two ways we can do it -- keeping set of leaves, or following sum structure.
;; Do the latter for now.

(defn choose-leaf [verified-summary]
  (->> (summary/extract-leaf-seq verified-summary (comp empty? summary/children))
       (map summary/source)
       (filter can-evaluate?)
       rand-nth))


(defn solve [root-subproblem]
  (summary/solve
   #(summaries/verified-summary root-subproblem summary/+worst-simple-summary+)
   (comp evaluate! choose-leaf)
   #(let [n (first (subproblem-name %))] (when-not (= (first n) :noop) n))))

(defn implicit-fah-a*-eval2 [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       solve))

(comment
  (defn pseudo-solve [root-sp]
   (summaries/pseudo-solve root-sp summary/+worst-simple-summary+ (complement summaries/expanded?)
                           #(if (evaluated? %) (do (assert (not (summaries/expanded? %))) (child-keys %)) (evaluate! %))))

  
  (defn implicit-fah-a*-eval-pseudo [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       subproblem/pseudo-solve)))




;; How should Or-summarize work?  There's no clear expand.
;; Instead, there should be two summaries -- local, and full.
;; Children live in local until they are evaluated, then they move to full.
;; Does this suggest two subproblems -- inner and outer ?

;; Both atomics and seqs have an OutputCollector tree.

