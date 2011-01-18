(ns angelic.search.summary-graphs
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList]))

;; This file defines an API for computing, caching, and propagating
;; summaries in a graph of summarizable objects, independent of the
;; generation of this search

;; Essentially, this gives the tools to easily implement AO*-type algorithms.

(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Node
  (add-child!     [n child-node])
  (remove-child!  [n child-node])
  (child-nodes    [n])

  (add-parent!    [n parent-node])
  (remove-parent! [n parent-node])
  (parent-nodes   [n])

  (add-subsumed!  [n subsumed-node])
  (subsumed-nodes [n]))

;; Basic idea here is to keep contents of summaries accurate, but children
;; may be stale.  i.e., call (comp summary source) in traversal.

(defprotocol SummaryCache
  (get-bound  [n])
  (add-bound! [n b])
  (summary [n]                      "Possibly cached version of summarize")
  (summary-changed! [n]             "Update summary and notify parents as needed")
  (summary-increased! [n]           "Increase summary and notify parents as needed")
  (summary-changed-local! [n]       "Just update local summary, no parent notification. Unsafe."))


(def *summary-count* (atom 0))

(defprotocol Summarizable
  (summarize [s] "Compute a summary based on the 'summary' of children, if applicable."))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Traits ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn remove! [^java.util.ArrayList list item]
  (let [i (util/position-if #(identical? % item) list)]
    (.remove list (int i))))

(traits/deftrait simple-node [] [^java.util.ArrayList children (java.util.ArrayList.)
                                 ^java.util.ArrayList parents  (java.util.ArrayList.)
                                 ^java.util.ArrayList subsumed (java.util.ArrayList.)] []
  Node
  (add-child!     [n c] (assert (not (identical? n c))) (.add children c))
  (remove-child!  [n c] (remove! children c))  
  (child-nodes    [n]   (seq children))
  
  (add-parent!    [n p] (.add parents p))
  (remove-parent! [n p] (remove! parents p))    
  (parent-nodes   [n]   (seq parents))
  
  (add-subsumed!  [n s] (.add subsumed s))
  (subsumed-nodes [n]   (seq subsumed)))


(defn connect! [parent child]
  (add-parent! child parent)
  (add-child! parent child))

(defn disconnect! [parent child]
  (remove-parent! child parent)
  (remove-child! parent child))

(defn connect-subsumed! [node subsumed-parent]
  (add-subsumed! node subsumed-parent)
  (summary node) ;; make sure we have a summary to bound?  TODO: this hurts perf lots in non-wa* case
  (add-bound! subsumed-parent (get-bound node))) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: Interaction between laziness and top-down bounds; 

;; TODO: pseudo-option ? (Correct Lazy seems untenable with top-down)

(def *subsumption* true)

(def *kill* false #_ true) ;; Remove dead children of OR-nodes.  Doesn't seem to really help or hurt...

(defn update-bound! [n bound-atom b]
  (when (and *subsumption* (< b @bound-atom))
    (util/print-debug 3 "UB" n @bound-atom b) 
    (reset! bound-atom b)
    (doseq [s (doall (subsumed-nodes n))]
      (add-bound! s b))
    true))

(defn update-summary! [n summary-atom bound-atom]
  (util/print-debug 3 "SUS" n  @summary-atom @bound-atom)
  (let [s (summarize n),
        r (summary/max-reward s)]
    (util/print-debug 3 "US" n  @summary-atom s @bound-atom)
   #_ (assert (<= r @bound-atom)) ;; TODO: put back
    (reset! summary-atom s)
    (update-bound! n bound-atom r) 
    s))

(traits/deftrait summary-cache [] [cache (atom nil) bound (atom 0)] []
  SummaryCache
  (get-bound        [n]   @bound)
  (add-bound!       [n b] (when (update-bound! n bound b) (summary-changed! n)))
  (summary [n] (or @cache  (update-summary! n cache bound)))
  (summary-changed! [n] 
    (when-let [old @cache]
;      (when-not (summary/viable? old) 
;      (util/assert-is (not (summary/viable? (summarize n))) "%s" [(def *bad* n) n old (summarize n)])) 
      (when  (summary/live? old) ;; TODO: this actually hurts for some reason...
        (when (not (summary/eq old (update-summary! n cache bound)))
#_          (util/assert-is (summary/live? old) "%s" [(def *bad* n) n]) ;; can put this in if we remove above check.
          (doseq [p (doall (parent-nodes n))]
            (summary-changed! p))))))  
  (summary-increased! [n] 
    (when-let [old @cache]
      (when  true #_ (summary/live? old) 
        (let [new (summarize n)]
          (cond (summary/eq old new) (reset! cache new) ;; Accomodate changed children for live pair...
                (summary/>= new old 0) (do (reset! cache new)
                                         (doseq [p (doall (parent-nodes n))]
                                           (summary-increased! p))))))))  
  (summary-changed-local! [n] (reset! cache (summarize n) #_ nil))) ;; TODO: bound? 

(traits/deftrait simple-cached-node [] [] [simple-node summary-cache])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait worst-summarizable [] [] []
  Summarizable (summarize [s] summary/+worst-simple-summary+))

(defn or-summary [n]
  (swap! *summary-count* inc)
  (if *kill*
    (let [[good-kids bad-kids] (util/separate #(summary/viable? (summary %)) (doall (child-nodes n)))]
      (doseq [k bad-kids] (remove-child! n k))
      (summary/or-combine-b (map summary good-kids) n (get-bound n)))    
    (summary/or-combine-b (map summary (child-nodes n)) n (get-bound n))))

(traits/deftrait or-summarizable [] [] []
  Summarizable (summarize [s] (or-summary s)))


(defn sum-summary [s]
  (swap! *summary-count* inc)
  (let [kids (child-nodes s)]
    (case (count kids)
      2 (summary/+ (summary (first kids)) (summary (second kids)) s (get-bound s))
      1 (summary/re-source (summary (first kids)) s (get-bound s) :solved))))

(defn make-sum-summarizer []
  (traits/reify-traits [simple-cached-node] Summarizable (summarize [s] (sum-summary s))))


(defn make-wrapping-summarizer [wrapped-node wrap-fn]
  (let [ret (traits/reify-traits [simple-cached-node]
              Summarizable (summarize [s] (wrap-fn s (summary wrapped-node))))]
    (connect! ret wrapped-node)
    ret))


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

(defn extract-single-live-leaf [summ choice-fn bound]
;  (println (summary/source summ) summ)
;  (assert (>= (summary/max-reward summ) bound)) ;; TODO: put back
;  (util/assert-is (summary/eq summ (-> summ summary/source summarize)) "%s" [(def *bad* summ)])
  (let [kids (map summary/source (summary/children summ))]
    (if (empty? kids)
      (summary/source summ)
      (let [live-kids (filter (comp summary/live? summary) kids)]
        (util/assert-is (seq live-kids) "%s" [(def *bad* summ)])
;        (util/assert-is (>= (reduce + (map (comp summary/max-reward summary) kids)) bound) "%s" [(def *bad* summ)])        
        (if-let [s (util/singleton live-kids)]
          (recur (summary s) choice-fn bound)
          (let [s (summary (choice-fn live-kids))]
            (recur s choice-fn (summary/max-reward s))))))))

(defn best-leaf-operator [choice-fn local-choice? op!-fn]
  #(op!-fn (if local-choice?
              (extract-single-live-leaf % choice-fn (summary/max-reward %))
              (choice-fn (extract-live-leaf-source-seq %)))))















