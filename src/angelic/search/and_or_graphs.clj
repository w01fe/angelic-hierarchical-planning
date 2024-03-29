(ns angelic.search.and-or-graphs
  (:require [angelic.util :as util]
            [angelic.util.queues :as queues]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList IdentityHashMap]))

;; Vs summary-graphs: 
;; Get rid of traits, and just use plain old functions or
;; maps of keys to functions.

;; vs summary-graphs-new:
;; Actually solve cycle problem, which arose when doing
;; weighted algortihms, previously hidden, by using LDFS-style algorithm.


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
#_  (summary node) ;; make sure we have a summary to bound?  TODO: this hurts perf lots in non-wa* case -- put back?
#_  (add-bound! subsumed-parent (get-bound node))) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *summary-counter* (atom 0))

(defn reset-counters [] (reset! *summary-counter* 0))

;; Basic idea here is to keep contents of summaries accurate, but children
;; may be stale.  i.e., call (comp summary source) in traversal.

(defn summarize [n] (swap! *summary-counter* inc) ((:summarize-fn n) n))

(def *subsumption* true)
;; note: must be careful about killing with kld.
(def *kill* false #_ true) ;; Remove dead children of OR-nodes.  Doesn't seem to really help or hurt...
(def *summary-count* (atom 0))



(defn make-summary-cache []
  {:summary-atom (atom nil)
   :bound-atom   (atom 0)})


;; Bounds are manually managed for now, only used with KLD.

(declare update-summary!)

(defn summary [n]
  (or @(:summary-atom n)
      (let [s (update-summary! n)]
        (reset! (:bound-atom n) (summary/max-reward s))
        s)))

(defn get-bound [n] 0 @(:bound-atom n))

(defn set-summary! [n s]
  (reset! (:summary-atom n) s))

(defn- update-summary! [n]
  (util/print-debug 4 "US" n @(:summary-atom n) (summarize n))
  (set-summary! n (summarize n)))




;; Just increase status, if you can do it without making parent worse.
;; Basic formula: take bounded summary.
;; Child can be better than parent, or worse.

;; Status can increase in update-summary-dec without changing parent b/c of inconsistencies.

(defn status-increased! [parent child]
  (when-let [ops @(:summary-atom parent)]
    (util/assert-is (= (summary/max-reward ops) @(:bound-atom parent))
                    (do (def *b* [parent child]) (pr-str  ops (summary child))))
    (let [cs (summary child)]
;      (println "SI"  parent #_ child ops cs #_ (summarize parent))
      (when (and (summary/live? ops) (not (summary/live? cs)))
        (let [nps (summarize parent)]
          (assert (<= (summary/max-reward nps) (summary/max-reward ops)))
          (when (and (= (summary/max-reward nps) (summary/max-reward ops))
                     (not (summary/live? nps)))
            (set-summary! parent nps)
            (doseq [gp (doall (seq (parent-nodes parent)))]
              (status-increased! gp parent))))))))



;; can produce suboptimal summaries
(defn- update-summary-inc?! [n]
  (when-let [old   (summary n)]
    (let [new (reset! (:summary-atom n) (summarize n))]
      (not (summary/>= old new 0)))))



(defn summaries-decreased! [active-nodes]
  (assert (= (count active-nodes) 1))
  (let [open  (IdentityHashMap.)
        all   (IdentityHashMap.)        
        q     (queues/make-fancy-tree-search-pq)
        cost  (fn [n] (let [s (summary n)] [(- (summary/max-reward s))
                                             (- (summary/status-val (summary/status s)))]))]
    ((fn add! [c]
       (when-not (.containsKey all c)
         (when-let [old @(:summary-atom c)]
           (let [new (update-summary! c)]
             (when (or (< (summary/max-reward new) (summary/max-reward old))
                       (not (summary/live? new)))
               (set-summary! c summary/+worst-simple-summary+)
               (.put all c true)
               (doseq [p (parent-nodes c)]
                 (add! p)))))))
     (first active-nodes))
     
     (doseq [n (keys all)]
       (when (update-summary-inc?! n)
         (.put open n true)
         (queues/pq-add! q n (cost n))))

     (while (not (queues/pq-empty? q)) ;; Can short circuit on dead too.
       (let [n (queues/pq-remove-min! q)]
         (.remove all n)
         (reset! (:bound-atom n) (summary/max-reward (summary n)))
         (util/print-debug 2 "SET" n (summary n))
         (doseq [p (parent-nodes n)]
           (when (.containsKey all p)
             (when (update-summary-inc?! p)
               (if (.containsKey open p)
                 (queues/pq-remove! q p)
                 (.put open p true))
               (queues/pq-add! q p (cost p)))))))

     (doseq [n (keys all)]
       (util/print-debug 2 "KILLING" n)
       (reset! (:bound-atom n) Double/NEGATIVE_INFINITY))))




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

(def or-summary-bws #(or-summarize % summary/or-combine-bws))


(defn sum-summary [s]
  (swap! *summary-count* inc)
  (let [kids (child-nodes s)]
    (assert (= (count kids) 2))
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



(defn ldfs! [root consistent-choice-fn bound op!-fn]
  (util/print-debug 1 "LDFS" root (summary root))
  (assert (summary/live? (summary root)))
  (when (summary/viable? (summary root) bound)
    (let [kids (summary/children (summary root))]
      (do (if (empty? kids)
            (op!-fn root)
            (when-let [cs (seq (filter (comp summary/live? summary summary/source) kids))];; TODO?
              (let [c (consistent-choice-fn cs)]
                (ldfs! (summary/source c) consistent-choice-fn (summary/max-reward c) op!-fn))))
          (update-summary! root)
          (reset! (:bound-atom root) (summary/max-reward (summary root)))
          (when (summary/live? (summary root))
            (recur root consistent-choice-fn bound op!-fn))))))
