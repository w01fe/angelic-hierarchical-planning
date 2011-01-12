(ns angelic.search.summaries
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
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
  (add-child!     [n child-node])
  (remove-child!  [n child-node])
  (child-nodes    [n])

  (add-parent!    [n parent-node])
  (remove-parent! [n parent-node])
  (parent-nodes   [n])

  (add-subsumed!  [n subsumed-node])
  (subsumed-nodes [n]))


(defprotocol SummaryCache
  (get-bound  [n])
  (add-bound! [n b])
  (summary [n]                      "Possibly cached version of summarize")
  (summary-changed! [n]             "Update summary and notify parents as needed")
  (summary-changed-local! [n]       "Just update local summary, no parent notification (pot'l unsafe)")
  (verified-summary [n min-summary] "Return a current exact best summary >= min-summary, or nil.
                                     Child sources will be correct but grandchildren may be stale.
                                     (i.e., call (comp summary source) on children if traversing)"))



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
  (add-child!     [n c] (.add children c))
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

;; TODO: correct?
(defn connect-subsumed! [node subsumed-parent]
  (add-subsumed! node subsumed-parent)
  (add-bound! subsumed-parent (get-bound node)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: Interaction between laziness and top-down bounds; 

;; TODO: pseudo-option ? (Correct Lazy seems untenable with top-down)

(def *subsumption* true)

(def *kill* true) ;; Remove dead children of OR-nodes.  Doesn't seem to really help or hurt...

(defn update-bound! [n bound-atom b]
  (when (and *subsumption* (< b @bound-atom))
#_    (println n @bound-atom b)
    (reset! bound-atom b)
    (doseq [s (doall (subsumed-nodes n))]
      (add-bound! s b))
    true))

(defn update-summary! [n summary-atom bound-atom]
  (let [s (summarize n),
        r (summary/max-reward s)]
#_    (println "US" n  @summary-atom s @bound-atom)
    (assert (<= r @bound-atom))
    (reset! summary-atom s)
    (update-bound! n bound-atom r)
    s))

;; TODO: assert consistency on nil cache, and with lazy...
(traits/deftrait summary-cache [] [cache (atom nil) bound (atom 0)] []
  SummaryCache
  (get-bound        [n]   @bound)
  (add-bound!       [n b] (when (update-bound! n bound b) (summary-changed! n)))
  (summary [n] (or @cache (update-summary! n cache bound)))
  (summary-changed! [n] #_(println "SC" n @cache @bound)
    (when-let [old @cache]
      (when (summary/live? old)
        (when (not (summary/eq old (update-summary! n cache bound)))          
          (doseq [p (doall (parent-nodes n))]
            (summary-changed! p))))))  
  (summary-changed-local! [n] (reset! cache nil))
  (verified-summary [n min-summary] 
    (let [cs (summary n)]
      (when (summary/>= cs min-summary)
        cs))))

(traits/deftrait simple-cached-node [] [] [simple-node summary-cache])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait worst-summarizable [] [] []
  Summarizable (summarize [s] summary/+worst-simple-summary+))


(defn or-summary [n]
  (swap! *summary-count* inc)
  (if *kill*
    (let [[good-kids bad-kids] (util/separate #(summary/viable? (summary %)) (doall (child-nodes n)))]
      (doseq [k bad-kids] (remove-child! n k))
      (summary/or-combine (map summary good-kids) n (get-bound n)))    
    (summary/or-combine (map summary (child-nodes n)) n (get-bound n))))

(traits/deftrait or-summarizable [] [] []
  Summarizable (summarize [s] (or-summary s)))


(defn sum-summary [s]
  (swap! *summary-count* inc)
  (let [[c1 c2 :as children] (child-nodes s)]
    (assert (= (count children) 2))
    (summary/+ (summary c1) (summary c2) s (get-bound s))))

(traits/deftrait sum-summarizable [] [] []
  Summarizable (summarize [s] (sum-summary s)))

(defn make-sum-summarizer [kids]
  (let [ret (traits/reify-traits [sum-summarizable simple-cached-node])]
    (doseq [kid kids] (connect! ret kid))
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
  (def *c* (atom 34))
  (summary/solve
    #(verified-summary root-summarizable summary/+worst-simple-summary+)
   #_#(do (when (<= (swap! *c* dec) 0) (assert nil))
        (verified-summary root-summarizable summary/+worst-simple-summary+))
   #(op!-fn (if local-choice?
             (extract-single-live-leaf % choice-fn)
             (choice-fn (extract-live-leaf-source-seq %))))
   action-extractor))













