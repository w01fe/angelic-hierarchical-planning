(ns angelic.search.summaries_old
  (:require [angelic.util :as util]
            [angelic.util.traits :as traits]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList]))

;; This file defines a dataflow-style API for computing and caching
;; summaries of potentially mutable objects.

;; The basic idea here is to separate these statistics and their
;; propagation and caching from the generation of the search space


(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Node
  (node-ordinary-children   [n])
  (node-subsuming-children  [n])
  (node-ordinary-parents   [n])
  (node-subsumed-parents   [n])    
  (add-parent!     [n parent-node sub?])
  (add-child!      [n child-node sub?])
  (remove-parent!     [n parent-node ])
  (remove-child!      [n child-node ])  )

(defprotocol SummaryCache
  (summary [n] "Possibly cached version of summarize")
  (summary-changed! [n] "Update summary and notify parents as needed")
  (summary-changed-local! [n] "Just update local summary, no parent notification (pot'l unsafe)")
  (verified-summary [n min-summary] "Return a current exact best summary >= min-summary, or nil.
                                     Child sources will be correct but grandchildren may be stale.
                                     (i.e., call (comp summary source) on children if traversing)"))



(def *summary-count* (atom 0))

(defprotocol Summarizable
  (summarize [s] "Compute a summary based on the 'summary' of children, if applicable."))

(def *use-subsumption* true)
(def *assert-consistency* false #_true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Traits ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-node [] [^java.util.ArrayList children (java.util.ArrayList.)
                                 ^java.util.ArrayList parents  (java.util.ArrayList.)] []
  Node
  (node-ordinary-children [n] (map second (remove first (seq children))))
  (node-subsuming-children [n] (map second (filter first (seq children))))
  (node-ordinary-parents [n] (map second (remove first (seq parents))))
  (node-subsumed-parents [n] (map second (filter first (seq parents))))    
  (add-child!    [n child subsuming?] (assert (not (identical? child n)))
    (.add children [subsuming? child]))
  (add-parent!   [n parent subsuming?] (assert (not (identical? parent n)))
    (.add parents [subsuming? parent]))
  (remove-child! [n child]
    (let [i (util/position-if #(identical? (second %) child) children)]
      (.remove children (int i))))  
  (remove-parent! [n parent]
    (let [i (util/position-if #(identical? (second %) parent) parents)]
      (.remove parents (int i))))  
  )

(traits/deftrait fixed-node [children] [^java.util.ArrayList sub-children (java.util.ArrayList.)
                                        ^java.util.ArrayList parents (java.util.ArrayList.)] []
   Node
   (node-ordinary-children [n] children)
   (node-subsuming-children [n] (seq sub-children))   
   (node-ordinary-parents [n] (map second (remove first (seq parents))))
   (node-subsumed-parents [n] (map second (filter first (seq parents))))    
   (add-child!    [n child sub?]
      (assert sub?)
      (.add sub-children child))
   (add-parent!   [n parent subsuming?] (.add parents [subsuming? parent]))
  (remove-child! [n child]
    (let [i (util/position-if #(identical? % child) sub-children)]
      (.remove sub-children (int i))))  
  (remove-parent! [n parent]
    (let [i (util/position-if #(identical? (second %) parent) parents)]
      (.remove parents (int i))))
   )



(defn connect! [parent child subsuming?]
  (when (or (not subsuming?) *use-subsumption*)
    (add-parent! child parent subsuming?)
    (add-child! parent child subsuming?)))

(defn disconnect! [parent child ]
  (remove-parent! child parent )
  (remove-child! parent child ))

(defn node-parents [n] (concat (node-ordinary-parents n) (node-subsumed-parents n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; This doesn't seem worth of a runtime option, make it compile-time.
(defn default-verified-summary [n min-summary]
  (let [cs (summary n)]
    (when (summary/>= cs min-summary 0)
      cs)))

(traits/deftrait uncached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (summarize n))
  (summary-changed! [n] nil)
  (summary-changed-local! [n] nil)
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))



;; Problem with making these true traits are that:
;; (1) no enforcement that all nodes use the same trait
;; (2) no way to select at runtime.

;; In retrospect, probably would be better to bite the bullet and say
;; "a node has a cache", but for now we just hack it with binding?

;; Note: Interaction between laziness and top-down bounds; 

;; TODO: pseudo-option ? 
;; TODO: (def *enforce-consistency* false)

(def *lazy-cache*    false ) 
(def *no-subsumption* false) ;; Don't notify subsumption parents
(def *assume-consistency* false) ;; Don't propagate lazy increases.  This often hurts without consistency enforcement...

;; TODO: assert consistency on nil cache, and with lazy...
(traits/deftrait summary-cache [] [cache (atom nil)] []
  SummaryCache
  (summary [n] (or @cache (do (reset! cache (summarize n)))))
  (summary-changed! [n]
    (when-let [old @cache]
      (when (summary/live? old)
        (let [new (summarize n)]
          (when *assert-consistency*
            (util/assert-is (<= (summary/max-reward new) (summary/max-reward old))))
          (reset! cache new)
          (when (cond (and *lazy-cache* *assume-consistency*) (not (summary/live? new))
                      *lazy-cache* (or (not (summary/>= old new 0)) (not (summary/live? new)))
                      :else        (not (summary/eq old new)))
            (doseq [p (doall ((if *no-subsumption* node-ordinary-parents node-parents) n))]
              (summary-changed! p)))))))
  (summary-changed-local! [n] (reset! cache nil #_ (summarize n)))
  (verified-summary [n min-summary] #_ (println "Verify" n min-summary)
   (if *lazy-cache*  
     (let [cs (summary n)] (assert nil) ;; Lazy not working currently, see discussion in dash_astar_opt. 
       (when (summary/>= cs min-summary 0)
         (if (or (not (summary/live? cs))
                 (every? #(verified-summary (summary/source %) %) (summary/children cs)))
           cs
           (let [ns (summarize n)]
             (when-not *assume-consistency* (util/assert-is (summary/>= cs ns 0) "%s" [(def *bad* n)]))
             (reset! cache ns)
             (recur min-summary)))))     
     (default-verified-summary n min-summary))))


(comment 

 ;; No notification, just pseudo-rbfs solution (which may refine suboptimal things)
 ;; Can't quite replicate earlier, since we don't have control over AND expansion order...
 ;; Can't use verified-summary since we need eval going up too.
 ;; TODO: improve min-summary handling ?
 ;; TODO: doesn't work right now, since deeper stuff doesn't get evaluated.
 ;; Need to think harder about separation of concerns, how to cross-cut ?
 (defprotocol PseudoSolver
   (pseudo-solve [n min-summary stop? evaluate!]))

(traits/deftrait pseudo-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n] (reset! summary-cache (summarize n)))
  (verified-summary [n min-summary] (throw (UnsupportedOperationException.)))
  PseudoSolver
  (pseudo-solve [n min-summary stop? evaluate!]
    (let [os @summary-cache
          cs (reset! summary-cache (summarize n))]
      (when os (assert (<= (summary/max-reward cs) (summary/max-reward os))))
      ;      (println min-summary cs (angelic.search.implicit.subproblem-eval/subproblem-name (summary/source cs)) (angelic.search.implicit.subproblem-eval/evaluated? (summary/source cs)) (expanded? (summary/source cs)) #_  (summary/source cs)) (Thread/sleep 10)
      (cond (not (summary/>= cs min-summary)) nil
            (summary/solved? cs) cs
            (stop? n) (do (println "\nEVAL!") (evaluate! n) (recur min-summary stop? evaluate!))
            :else (let [child (util/safe-singleton (summary/children cs))]
                    (pseudo-solve (summary/source child) child stop? evaluate!)
                    (recur min-summary stop? evaluate!)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; Note: this entails zero minimum cost (i.e., nonnegative costs).
(defn subsuming-bound [s]
  (->> (node-subsuming-children s)
       (map (comp summary/max-reward summary))
       (apply min 0)))

(defn or-summary [s b]
  (swap! *summary-count* inc)
  (summary/or-combine (map summary (node-ordinary-children s))
                      s (min (subsuming-bound s) b)))


(traits/deftrait or-summarizable [] [] []
  Summarizable (summarize [s] (or-summary s 0)))

(traits/deftrait simple-cached-node [] [] [simple-node summary-cache])

(defn sum-summary [s b]
  (swap! *summary-count* inc)
  (let [children (node-ordinary-children s)]
    (assert (= (count children) 2))
    (summary/+ (summary (first children)) (summary (second children))
               s (min b (subsuming-bound s)))))

(traits/deftrait sum-summarizable [] [] []
  Summarizable (summarize [s] (sum-summary s 0)))

(defn make-sum-summarizer [kids]
  (let [ret (traits/reify-traits [sum-summarizable simple-cached-node])]
    (doseq [kid kids] (connect! ret kid false))
    ret))

(traits/deftrait worst-summarizable [] [] []
  Summarizable (summarize [s] summary/+worst-simple-summary+))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searching ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn extract-live-leaf-source-seq [summ]
  (let [l   (ArrayList.) ;; functional version slow for some reason...
        dfs (fn dfs [summ]
              (if-let [kids (seq (summary/children summ))]
                (let [fresh-kids (map (comp summary summary/source) kids)
                      live-kids (filter summary/live? fresh-kids)]
                  (doseq [c live-kids] (dfs c)))
                (.add l (summary/source summ))))]
    (dfs summ)
    (seq l)))

(defn extract-single-live-leaf [summ choice-fn]
  (let [kids (map summary/source (summary/children summ))]
    (if (empty? kids)
      (summary/source summ)
      (let [live-kids (filter (comp summary/live? summary) kids)]
        (util/assert-is (seq live-kids) "%s" [(def *bad* summ)])
        (recur (summary (or (util/singleton live-kids) (choice-fn live-kids))) choice-fn)))))


(def *root* nil)
(defn solve [root-summarizable choice-fn local-choice? op!-fn action-extractor]
  (def *root* root-summarizable)
  (summary/solve
   #(verified-summary root-summarizable summary/+worst-simple-summary+)
   #(op!-fn (if local-choice?
             (extract-single-live-leaf % choice-fn)
             (choice-fn (extract-live-leaf-source-seq %))))
   action-extractor))

;; What should bthe interface be ? Choose shallowest ?
;; Maybe two -- 











