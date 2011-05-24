(ns angelic.search.summary-graphs-new
  (:require [angelic.util :as util]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList]))

;; Vs summary-graphs: 
;; Get rid of traits, and just use plain old functions or
;; maps of keys to functions.

;; This file defines an API for computing, caching, and propagating
;; summaries in a graph of summarizable objects, independent of the
;; generation of this search

;; Essentially, this gives the tools to easily implement AO*-type algorithms.

(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Node  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare summary get-bound add-bound!)

(defn remove! [^java.util.ArrayList list item]
  (let [i (util/position-if #(identical? % item) list)]
    (.remove list (int i))))

(defn make-node []
  {:children (ArrayList.)
   :parents  (ArrayList.)
   :subsumed (ArrayList.)})


(defn- l-add! [p k c]
  (util/assert-is (not (identical? p c)))
  (.add ^ArrayList (k p) c))

(defn- l-remove! [p k c]
  (let [list ^ArrayList (k p)
        i (util/position-if #(identical? % c) list)]
    (.remove list (int i))))

(defn- l-nodes [p k] (seq ^ArrayList (k p)))


(defn add-child!     [p c] (l-add! p :children c))
(defn remove-child!  [p c] (l-remove! p :children c))
(defn child-nodes    [p]   (l-nodes p :children))

(defn add-parent!    [p c] (l-add! p :parents c))
(defn remove-parent! [p c] (l-remove! p :parents c))
(defn parent-nodes   [p]   (l-nodes p :parents))

(defn add-subsumed!  [p c] (l-add! p :subsumed c))
(defn subsumed-nodes [p]   (l-nodes p :subsumed))

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

;; Basic idea here is to keep contents of summaries accurate, but children
;; may be stale.  i.e., call (comp summary source) in traversal.

(defn summarize [n] ((:summarize-fn n) n))

(def *subsumption* true)
(def *kill* true) ;; Remove dead children of OR-nodes.  Doesn't seem to really help or hurt...
(def *summary-count* (atom 0))


;; Note: Interaction between laziness and top-down bounds; 
;; TODO: pseudo-option ? (Correct Lazy seems untenable with top-down)

(defn make-summary-cache []
  {:summary-atom (atom nil)
   :bound-atom   (atom 0)})

(defn- update-bound! [n b]
  (let [bound-atom (:bound-atom n)]
   (when (and b *subsumption* (< b @bound-atom))
     (util/print-debug 3 "UB" n @bound-atom b) 
     (reset! bound-atom b)
     (doseq [s (doall (subsumed-nodes n))]
       (add-bound! s b))
     true)))

(defn- update-summary! [n]
  (let [bound-atom (:bound-atom n)
        summary-atom (:summary-atom n)]
   (util/print-debug 3 "SUS" n  @summary-atom @bound-atom)
   (let [s (summarize n),
         r (summary/max-reward s)]
     (util/print-debug 3 "US" n  @summary-atom s @bound-atom)
     (when r (util/assert-is (<= r @bound-atom) "%s" [n r @bound-atom (def *bad* n)]))
     (reset! summary-atom s)
     (update-bound! n r) 
     s)))


(defn summary [n] (or @(:summary-atom n) (update-summary! n)))

(defn summary-changed! [n]
  (util/print-debug 4 "SC" n )
  (let [cache (:summary-atom n)
        bound (:bound-atom n)]
    (when-let [old @cache]
       (when  (summary/live? old) ;; TODO: this actually hurts for some reason...
         (when (not (summary/eq old (update-summary! n)))
           (doseq [p (doall (parent-nodes n))]
             (summary-changed! p)))))))

(defn summary-increased! [n]
  (util/print-debug 4 "SI" n)
  (let [cache (:summary-atom n)
        bound (:bound-atom n)]
   (when-let [old @cache]
     (when true 
       (let [new (summarize n)]
         (cond (summary/eq old new) (reset! cache new) ;; Accomodate changed children for live pair...
               (summary/>= new old 0) (do (reset! cache new)
                                          (doseq [p (doall (parent-nodes n))]
                                            (summary-increased! p)))))))))

(defn summary-changed-local! [n] (reset! (:summary-atom n) (summarize n)))

(defn get-bound [n] @(:bound-atom n))

(defn add-bound! [n b] (when (update-bound! n b) (summary-changed! n)))


(defn make-simple-cached-node []
  (merge (make-node) (make-summary-cache)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn or-summarize [n combine-fn]
  (swap! *summary-count* inc)
  (if *kill*
    (let [[good-kids bad-kids]
          (util/separate #(summary/viable? (summary %)) (doall (child-nodes n)))]
      (doseq [k bad-kids] (remove-child! n k))
      (combine-fn (map summary good-kids) n (get-bound n)))    
    (combine-fn (map summary (child-nodes n)) n (get-bound n))))


(def or-summary #(or-summarize % summary/or-combine-b))


(defn sum-summary [s]
  (swap! *summary-count* inc)
  (let [kids (child-nodes s)]
    (summary/+ (summary (first kids)) (summary (second kids)) s (get-bound s))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searching ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn extract-live-leaf-source-seq [summ]
  (let [l   (ArrayList.) 
        dfs (fn dfs [summ]
              (if-let [kids (seq (summary/children summ))]
                (let [fresh-kids (map (comp summary summary/source) kids)
                      live-kids (filter summary/live? fresh-kids)]
                  (doseq [c live-kids] (dfs c)))
                (.add l (summary/source summ))))]
    (dfs summ)
    (seq l)))

(defn extract-single-live-leaf [summ choice-fn bound]
  (let [kids (map summary/source (summary/children summ))]
    (if (empty? kids)
      (summary/source summ)
      (let [live-kids (filter (comp summary/live? summary) kids)]
        (util/assert-is (seq live-kids) "%s" [(def *bad* summ)])
        (if-let [s (util/singleton live-kids)]
          (recur (summary s) choice-fn bound)
          (let [s (summary (choice-fn live-kids))]
            (recur s choice-fn (summary/max-reward s))))))))

(defn best-leaf-operator [choice-fn local-choice? op!-fn]
  #(op!-fn (if local-choice?
              (extract-single-live-leaf % choice-fn (summary/max-reward %))
              (choice-fn (extract-live-leaf-source-seq %)))))










