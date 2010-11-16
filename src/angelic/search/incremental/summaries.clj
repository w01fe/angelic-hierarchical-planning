(ns angelic.search.incremental.summaries
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.incremental.summary :as summary]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Node
  (node-children   [n])
  (node-parents    [n])
  (add-parent!     [n parent-node])
  (add-child!      [n child-node]))

(defprotocol SummaryCache
  (summary [n] "Possibly cached version of summarize")
  (summary-changed! [n])
  (verified-summary [n min-summary] "Produce a summary that represents the current exact best summary, or
                                     something workse than min-summary if not feasible."))


(defprotocol Expandable
  (expanded?   [s])
  (expand!     [s children]))

(defprotocol Summarizable
  (summarize [s] "Compute a summary based on the 'summary' of children, if applicable."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Traits ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-node [] [children (atom nil) parents  (atom nil)] []
  Node
  (node-children [n] @children)
  (node-parents  [n] @parents)
  (add-child!    [n child] (swap! children conj child))
  (add-parent!   [n parent] (swap! parents conj parent)))

(traits/deftrait fixed-node [children] [parents  (atom nil)] []
  Node
  (node-children [n] children)
  (node-parents  [n] @parents)
  (add-child!    [n child] (throw (UnsupportedOperationException.)))
  (add-parent!   [n parent] (swap! parents conj parent)))

(defn connect! [parent child] (add-parent! child parent) (add-child! parent child))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; NOTE: These all assume that the entire tree uses the same trait.

(traits/deftrait uncached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (summarize n))
  (summary-changed! [n] nil)
  (verified-summary [n min-summary] (summary n)))

(traits/deftrait eager-cached-summarizer-node [] [summary-cache (atom nil)] []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (when-not (= @summary-cache (reset! summary-cache (summarize n)))
      (doseq [p (node-parents n)] (summary-changed! p))))
  (verified-summary [n min-summary] (summary n)))

;; Only notifies when summary increases ...
;; Need a way to know which child(ren) summary computation depended on.
;; How is this different from sources?
;; Answer: for a seq, want to expand seq node, but verify against constituents.
(traits/deftrait lazy-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (when-not (summary/>= @summary-cache (reset! summary-cache (summarize n)))
      (doseq [p (node-parents n)] (summary-changed! p))))
  (verified-summary [n min-summary]
    (let [cs (summary n)]
      (if (or (not (summary/>= cs min-summary))
              (empty? (summary/children cs)))
        cs
        (do (doseq [child (summary/children cs)] (verified-summary (summary/source child) child))
            (summary-changed! n)
            (recur min-summary))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Expandable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-expandable [] [expanded?-atom (atom false)] []
  Expandable
  (expanded? [s] @expanded?-atom)
  (expand!   [s child-summarizers]
    (assert (not (expanded? s)))
    (reset! expanded?-atom true)
    (doseq [child child-summarizers] (connect! s child))
    (child-changed! s :all)))
;; What should this really be ? 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Trait or concrete ?
(traits/deftrait const-summarizable [reward status] [] []
  Summarizable
  (summarize [s] (summary/make-simple-summary reward status s)))

;; Initially shoud be a parent of init, without having child.
(traits/deftrait simple-or-summarizable [init] [] [simple-expandable]
  Summarizable
  (summarize [s]
    (if (expanded? s)
      (summary/bound (apply summary/max (map summary (node-children s))) (summary/max-reward (summary init)))
      (summary/adjust-source (summary init) s))))

;; This one is not expandable, needs children set from outside
(traits/deftrait simple-seq-summarizable [] [] []
  Summarizable
  (summarize [s] (apply summary/sum (map summary (node-children s)))))



;; Concerns:
;; computing a summary given children
;; When to use cached/fresh
;; verifying that (cached) summary is good enough. --> should be above

(defn make-const-summarizable [reward status]
  (traits/reify-traits [simple-node uncached-summarizer-node (const-summarizable reward status)]))









(comment

 (defprotocol Summarizable
   (summary  [s] "Return a summary.  May change over time.")
   (expand!  [s] "???"))

; Always has form min(..., max(...)) or sum(...)? 
 (defprotocol Node
   (node-type       [s] ":or, :and, or :leaf")
   (current-summary [s] "Return the current cached summary.")
   (compute-summary [s] "Compute a fresh summary, without interacting with cache.")
   (notify!         [s child] "Notify that the summary of a child has changed."))

 (defprotocol PLeafNode
   )

 (defprotocol POrNode
   (max-child      [s] "Return child with best (possibly stale) summary.")
   (second-summary [s] "Return the (possibly stale) summary of second-best child.")
   #_ "add child?? expand-leaf-child??")

 (defprotocol PAndNode
   (best-child     [s summary-value-fn])
   #_ "???"
   )

 (deftype OrNode
   [upper-bound
    ^{:unsynchronized-mutable true} children]
   )

 (defn make-or-node [upper-bound init-children])




 (defn compute-sum-summary [children] (reduce summary/+ (map current-summary children)))
 (defn compute-sum-summary [children] (reduce summary/+ (map current-summary children)))

 (deftype SumSummarizer [^{:volatile-mutable true} cached-summary children parents]
   (compute-summary [s] (reduce summary/+ (map current-summary children)))
   ))







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
