(ns angelic.search.summaries
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.summary :as summary]))

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
  (node-ordinary-children   [n])
  (node-subsuming-children   [n])  
  (node-parents    [n])
  (add-parent!     [n parent-node])
  (add-child!      [n child-node sub?]))

(defprotocol SummaryCache
  (summary [n] "Possibly cached version of summarize")
  (summary-changed! [n])
  (verified-summary [n min-summary] "Produce a summary that represents the current exact best summary, or
                                     something workse than min-summary if not feasible."))

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

(traits/deftrait simple-node [] [children (atom nil) parents  (atom nil)] []
  Node
  (node-ordinary-children [n] (map second (remove first @children)))
  (node-subsuming-children [n] (map second (filter first @children)))  
  (node-parents  [n] @parents)
  (add-child!    [n child subsuming?] (swap! children conj [subsuming? child]))
  (add-parent!   [n parent] (swap! parents conj parent)))

(traits/deftrait fixed-node [children] [sub-children (atom nil) parents (atom nil)] []
   Node
   (node-ordinary-children [n] children)
   (node-subsuming-children [n] @sub-children)   
   (node-parents  [n] @parents)
   (add-child!    [n child sub?]
      (assert sub?)
      (swap! sub-children conj child))
   (add-parent!   [n parent] (swap! parents conj parent)))

(def *use-subsumption* true)

(defn connect! [parent child subsuming?]
 ;  (when subsuming? (print "."))
  (when (or (not subsuming?) *use-subsumption*)
    (add-parent! child parent)
    (add-child! parent child subsuming?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn notify-parents [n] (doseq [p (node-parents n)] (summary-changed! p)))

;;; NOTE: These all assume that the entire tree uses the same trait.

(traits/deftrait uncached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (summarize n))
  (summary-changed! [n] nil)
  (verified-summary [n min-summary] (summary n)))

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
      ;;      (println (count (node-parents n)))
      ;;      (when (> (count (node-parents n)) 1) (println n))
      (doseq [p (node-parents n)] (summary-changed! p))))
  (verified-summary [n min-summary] (summary n)))

;; Only notifies when summary increases ...
;; Need a way to know which child(ren) summary computation depended on.
;; How is this different from sources?
;; Answer: for a seq, want to expand seq node, but verify against constituents.
;; TODO: this is broken, since updates never make it upwards along OR-nodes... 
(traits/deftrait lazy-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (when-not (summary/>= @summary-cache (reset! summary-cache (summarize n)))
      (notify-parents n)))
  (verified-summary [n min-summary]
    (let [cs (reset! summary-cache (summarize n))]
;      (println (angelic.search.implicit.subproblem/subproblem-name n) (expanded? n) cs min-summary) (Thread/sleep 10)
      (if (or (not (summary/>= cs min-summary))
              (every? #(summary/>= (verified-summary (summary/source %) %) %) (summary/children cs)))
        cs
        (recur min-summary)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn bound-subsuming [s sum]
  (summary/bound sum (summary/max-reward (apply summary/min (map summary (node-subsuming-children s))))))

(defn bound-subsuming-x [s sum extra-bound]
  (summary/bound sum (min extra-bound (summary/max-reward (apply summary/min (map summary (node-subsuming-children s)))))))

(defprotocol LeafSummarizable (adjust-summary [s new-reward new-status]))

(traits/deftrait leaf-summarizable [reward status] [pair-atom (atom [reward status])] []
  Summarizable
  (summarize [s]
   (swap! *summary-count* inc)
   (let [[rew st] @pair-atom] (summary/make-simple-summary rew st s)))
  LeafSummarizable
  (adjust-summary [s new-rew new-st] (reset! pair-atom [new-rew new-st]) (summary-changed! s)))
;; Note: no need for bound-subsuming here. 

(comment
 (defn make-leaf-summarizable [reward status]
   (traits/reify-traits [simple-node uncached-summarizer-node (leaf-summarizable reward status)]))

 (def worst-summarizable (make-leaf-summarizable Double/NEGATIVE_INFINITY :blocked)))




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
     (let [init-summary (summary init)]
       (bound-subsuming s
         (if (not (and (summary/live? init-summary) (expanded? s)))
           (summary/adjust-source init-summary s)
           (summary/bound (summary/apply-max (doall (map summary (node-ordinary-children s))))
                      (summary/max-reward init-summary)))))))


;; This one is not expandable, needs children set from outside
(traits/deftrait simple-seq-summarizable [] [] []
  Summarizable
  (summarize [s]
   (swap! *summary-count* inc)
   (bound-subsuming s (apply summary/sum (map summary (node-ordinary-children s))))))

(defprotocol ExpandingPairSummarizable (set-right! [s right]))

(def +zero-live+ (summary/make-live-simple-summary 0 :dummy))

(traits/deftrait expanding-pair-summarizable [left] [right-atom (atom nil)] []
  Summarizable
  (summarize [s]
    (swap! *summary-count* inc)         
    (bound-subsuming s (if-let [right @right-atom]
                         (apply summary/sum (map summary [left right]))
                         (summary/sum (summary left) +zero-live+))))
  
  ExpandingPairSummarizable
  (set-right! [s right] (reset! right-atom right)))





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