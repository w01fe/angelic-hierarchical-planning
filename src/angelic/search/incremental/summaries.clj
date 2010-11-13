(ns angelic.search.incremental.summaries
  (:require [edu.berkeley.ai.util :as util]
            [angelic.search.incremental.summary :as summary]))

;; This file defines a dataflow-style API for computing and caching
;; summaries of potentially mutable objects.

;; The basic idea here is to separate these statistics and their
;; propagation and caching from the underlying search space.

;; Ideally, this would define a trait that lived inside Summarizables ? 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Actually, leaves have fixed summaries?  Except "live" can change - "increase" to blocked.
;; TODO: if we do eager propagation, how do we avoid infinite loops ? 

(defprotocol Summarizer
  (initialize! [s init-summary])
  (summarize   [s])
  (expanded?   [s])
  (expand!     [s children]))



;; No caching or anything...
(defn make-simple-summarizer []
  (let [summary-atom (atom :uninitialized)
        children-atom (atom :unexpanded)]
    (reify
     Summarizer
     (initialize! [s init]
       (assert (= @summary-atom :uninitialized))
       (reset! summary-atom init))
     (summarize [s]
       (if (= @children-atom :unexpanded)
         @summary-atom
         (summary/bound (apply summary/max (map summarize @children-atom))
                        (summary/max-reward @summary-atom))))
     (expanded? [s] (not (= @children-atom :unexpanded)))
     (expand!   [s child-summarizers]
       (assert (summary/live? @summary-atom))
       (assert (not (expanded? s)))
       (reset! children-atom child-summarizers)))))




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
