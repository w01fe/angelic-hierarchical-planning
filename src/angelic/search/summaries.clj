(ns angelic.search.summaries
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList]))

;; This file defines a dataflow-style API for computing and caching
;; summaries of potentially mutable objects.

;; The basic idea here is to separate these statistics and their
;; propagation and caching from the underlying search space.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Actually, leaves have fixed summaries?  Except "live" can change - "increase" to blocked.
;; TODO: if we do eager propagation, how do we avoid infinite loops ?

;; Also; regardless of caching, etc; need way to verify that an apparently-optimal
;; plan is actually optimal before doing any refinement 

;; Either summarizer needs atom for source, and stash it in summary,
;; or source needs atom for summarizer.
;; Either way is a bit of a pain.  Former is maybe better ?

;; How do we seprate out dependence from physics ? 

;; TODO: notify and extract go logically together ??

;; Separation of concerns:
;; And/OR/const. -- computing summaries
;; Caching and notification strategy

;; Main concern: how do cached values get into computing?
;; notifier should have getChildSummaries, or some such ...

;; Three types of caching behavior:
;; None -- compute fresh, recursively, every time.
;; full -- always fully propagate changes to the top, just use cached values as accurate.
;; Lazy -- report cache, ...

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
  (add-child!      [n child-node sub?]))

(defprotocol SummaryCache
  (summary [n] "Possibly cached version of summarize")
  (summary-changed! [n])
  (verified-summary [n min-summary] "Return a current exact best summary >= min-summary, or nil"))


(def *summary-count* (atom 0))


(defprotocol Summarizable
  (summarize [s] "Compute a summary based on the 'summary' of children, if applicable."))

;; New-bound is a summarizable.
(defprotocol Expandable
  (expanded?   [s])
  (expand!     [s children]))

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
    (.add parents [subsuming? parent])))

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
   (add-parent!   [n parent subsuming?] (.add parents [subsuming? parent])))

(def *use-subsumption* true)

(defn connect! [parent child subsuming?]
 ;  (when subsuming? (print "."))
  (when (or (not subsuming?) *use-subsumption*)
    (add-parent! child parent subsuming?)
    (add-child! parent child subsuming?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn node-parents [n] (concat (node-ordinary-parents n) (node-subsumed-parents n)))
(defn notify-parents [n] (doseq [p (node-parents n)] (summary-changed! p)))
(defn notify-ordinary-parents [n] (doseq [p (node-ordinary-parents n)] (summary-changed! p)))

;;; NOTE: These all assume that the entire tree uses the same trait.

(defn default-verified-summary [n min-summary]
  (let [cs (summary n)]
    (when (summary/>= cs min-summary)
      cs)))

(traits/deftrait uncached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (summarize n))
  (summary-changed! [n] nil)
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))

;; TODO: fix this up ?
(defn update-cache! [n cache-atom]
  (let [old @cache-atom new (summarize n)]
    (when-not (and old (summary/solved? old)) 
     (when old
       ;;      (util/assert-is (not (summary/solved? old)) "%s" [(def *bad* [old new])])
       (util/assert-is (<= (summary/max-reward new) (summary/max-reward old)) "%s" [(def *bad* n)])
       ;;      (println (= old new) (summary/eq old new) (summary/>= old new) old new)
       )
     (reset! cache-atom new)
     (not (= old new)))))

(traits/deftrait eager-cached-summarizer-node [] [summary-cache (atom nil)] []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]    
    (when (update-cache! n summary-cache)
      (notify-parents n)))
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))

;; Eager except about subsumption, which is just accidental
(traits/deftrait less-eager-cached-summarizer-node [] [summary-cache (atom nil)] []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]    
    (when (update-cache! n summary-cache)
      (notify-ordinary-parents n)))
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))



;; Only notifies when summary increases ...
;; TODO: figure out best v-s method.
;; NOTE: efficiency depends on consistency of child ordering ...
(traits/deftrait lazy-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (let [os @summary-cache
          ns (reset! summary-cache (summarize n))]
      (when os
        (assert (<= (summary/max-reward ns) (summary/max-reward os)))      
        (when-not (summary/>= os ns)
;          (print (summary/status ns))
          (notify-parents n)))))
  (verified-summary [n min-summary]
     (let [os @summary-cache
           cs (reset! summary-cache (summarize n))]
;       (swap! *summary-count* dec)
       (when os (util/assert-is (<= (summary/max-reward cs) (summary/max-reward os))))
;      (println (angelic.search.implicit.subproblem/subproblem-name n) (expanded? n) cs min-summary) (Thread/sleep 10)
;      (println n os cs min-summary) (Thread/sleep 10)       
       (when (summary/>= cs min-summary)
         (let [verified-children (map #(verified-summary (summary/source %) %) (summary/children cs))]
           (if (every? identity verified-children)
             (reset! summary-cache (summary/re-child cs verified-children))
             (recur min-summary)))))))


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
                    (recur min-summary stop? evaluate!))))))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol LeafSummarizable
  (label [s])
  (adjust-summary [s new-reward new-status]))

(traits/deftrait leaf-summarizable [label reward status] [pair-atom (atom [reward status])] []
  Summarizable
  (summarize [s]
   (swap! *summary-count* inc)
   (let [[rew st] @pair-atom] (summary/make-simple-summary rew st s)))
  LeafSummarizable
  (label [s] label)
  (adjust-summary [s new-rew new-st] (reset! pair-atom [new-rew new-st]) (summary-changed! s)))

;; Note: no need for bound-subsuming here. 

(comment
 (defn make-leaf-summarizable [reward status]
   (traits/reify-traits [simple-node uncached-summarizer-node (leaf-summarizable reward status)]))
)

(def worst-summarizable
     (traits/reify-traits [(leaf-summarizable :worst Double/NEGATIVE_INFINITY :blocked)
                           (fixed-node nil) uncached-summarizer-node] ))



;; Initially shoud be a parent of init, without having child.

(traits/deftrait simple-or-summarizable [init] [expanded?-atom (atom false)] []
   Expandable
   (expanded? [s] @expanded?-atom)
   (expand!   [s child-summarizers]
     (assert (not (expanded? s)))
     (reset! expanded?-atom true)
     (doseq [child child-summarizers] (connect! s child false))
     (summary-changed! s))
   Summarizable
   (summarize [s]
     (swap! *summary-count* inc)
     (let [init-summary (summary init)
           bound        (summary/max-reward (apply summary/min (map summary (node-subsuming-children s))))]
       (if (not (and (summary/live? init-summary) (expanded? s)))
         (summary/or-combine [init-summary] s bound)
         (summary/or-combine (map summary  (node-ordinary-children s)) s (min bound (summary/max-reward init-summary)))))))

(defn extract-unexpanded-leaf [summary]
  (summary/extract-single-leaf summary #(not (expanded? (summary/source %)))))

(defn extract-verified-unexpanded-leaf [summarizable]
  (let [s (verified-summary summarizable summary/+worst-simple-summary+)]
    (if (summary/solved? s) s (extract-unexpanded-leaf s))))


;; These ones need children set from outside...

(defprotocol ExpandingPairSummarizable (set-right! [s right]))

(traits/deftrait expanding-pair-summarizable [left right?] [right-atom (atom right?)] []
  Summarizable
  (summarize [s]
    (swap! *summary-count* inc)         
    (assert (empty? (node-subsuming-children s)))
    (if-let [right @right-atom]
      (summary/+ (summary left) (summary right) s)
      (summary/liven (summary left) s)))
  
  ExpandingPairSummarizable
  (set-right! [s right] (reset! right-atom right)))

(traits/deftrait simple-pair-summarizable [left right] [] [(expanding-pair-summarizable left right)])





;; Concerns:
;; computing a summary given children
;; When to use cached/fresh
;; verifying that (cached) summary is good enough. --> should be above








(comment
  (defn extract-best-and-summaries
   "Return [best-item best-summary rest-items rest-summary]"
   [summary-fn things]
   (assert (seq things))
   (loop [best-thing   (first things)
          best-summary (summary-fn (first things))
          rest-things  []
          rest-summary  +worst-summary+
          more-things  (rest things)]
     (if-let [[next-thing & even-more-things] (seq more-things)]
       (let [next-summary (summary-fn next-thing)]
         (if (better-summary? next-summary best-summary)
           (recur next-thing next-summary
                  (conj rest-things best-thing) best-summary even-more-things)
           (recur best-thing best-summary
                  (conj rest-things next-thing) (max-summary next-summary rest-summary) even-more-things)))
       [best-thing best-summary rest-things rest-summary]))))


(defmacro assert-valid-summary-change
  ([old-summary new-summary] ( assert-valid-summary-change old-summary new-summary ""))
  ([old-summary new-summary msg]
     `(do (util/assert-is (<= (max-reward ~new-summary) (max-reward ~old-summary)) "%s" [~old-summary ~new-summary ~msg])
        (when-not (live? ~old-summary) (assert (= ~old-summary ~new-summary))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Expandable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment
  (traits/deftrait simple-expandable [] [expanded?-atom (atom false)] []
   Expandable
   (expanded? [s] @expanded?-atom)
   (expand!   [s child-summarizers]
              (assert (not (expanded? s)))
              (reset! expanded?-atom true)
              (doseq [child child-summarizers] (connect! s child false))
              (summary-changed! s))))