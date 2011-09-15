(ns angelic.search.summary-graphs-newer
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

;; Basic idea here is to keep contents of summaries accurate, but children
;; may be stale.  i.e., call (comp summary source) in traversal.

(defn summarize [n] ((:summarize-fn n) n))

(def *subsumption* true)
;; TODO: can't kill with KLD.
(def *kill* false #_ true) ;; Remove dead children of OR-nodes.  Doesn't seem to really help or hurt...
(def *summary-count* (atom 0))


;; Note: Interaction between laziness and top-down bounds; 
;; TODO: pseudo-option ? (Correct Lazy seems untenable with top-down)

(defn make-summary-cache []
  {:summary-atom (atom nil)
   :bound-atom   (atom 0)})

;; Ignore bounds for now, figure out how to add them back later.
;; (they're a bit tricky with KLD stuff, since we temporarily do cost increases...)

(declare update-summary!)

(defn summary [n]
  (or @(:summary-atom n) (update-summary! n)))

(defn get-bound [n] @(:bound-atom n))
(defn add-bound! [n b] ::TODO)


(comment
 (let [h (java.util.IdentityHashMap.)]
  (defn atomic-cost [n]
    (or (get h n)
        (let [c
              (second
                (angelic.search.implicit.ah-astar/optimistic-ah-a-part*
                 (second (:input-sets n))
                 (second (:name n))))
              #_
              (try
               
               (catch AssertionError e (println e) -100000)
               )]
          (.put h n c)
          c))))
  
 (defn check-cost! [n s]
   (when-not (= (summary/max-reward s) Double/NEGATIVE_INFINITY)
     (when-let [n (:ts-sp n)]
       (when (= (first (:name n)) :Atomic)
         (when (angelic.hierarchy.state-set/singleton (second (:input-sets n)))
           (when (nil? @(:summary-atom n)) (println "DANGER?"))
           (let [o (atomic-cost n)]
             (when (< (summary/max-reward s) (or o -100000))
               (println n o s)
               (def *flub* [n o s])
               (throw (RuntimeException. "SUX"))))))))))

(defn set-summary! [n s]
#_  (check-cost! n s)
  (reset! (:summary-atom n) s))



;; TODO: just try lumping all together for now?
;; Called when child is just added as new child of parent.
;; Status of child may increase status of parent.
;; Propagate this upwards as status increases and cost does not decrease.
;; Cost increases are not allowed.  This must only change statuses in the
;; tree (and perhaps children?) -- rewards must not change.
;; However, can use some other intuitions as well?
;; I.e., when a node marked solved, its cost must be right (ie no cycles)
;; Same is true for blocked. 
(defn status-increased! [parent child]
  (when @(:summary-atom parent) ;; TODO: correct?
    (let [cs (summary child)
          ops (summary parent)]
      (when (> (summary/status-val (summary/status cs))
               (summary/status-val (summary/status ops)))
        (let [nps (summarize parent)]
          #_ (println "SI" (:name parent) (:name child) cs ops nps
                      (map summary (parent-nodes parent))
                      (map summarize (parent-nodes parent))                 
                      )

                                        ;        (println parent ops nps) (Thread/sleep 100)
          (when (>= (summary/max-reward nps) (summary/max-reward ops)) ;; accomodate pair case.
            (util/assert-is (= (summary/max-reward nps) (summary/max-reward ops)) "%s" (def *bad* [parent child]))
            (set-summary! parent nps) #_ (reset! (:summary-atom parent) nps)
            (when (> (summary/status-val (summary/status nps))
                     (summary/status-val (summary/status ops)))
              (doseq [gp (doall (seq (parent-nodes parent)))] ;; TODO: comodification in pair -- safe?
                (status-increased! gp parent)))))))))

(defn- update-summary! [n]
  (util/print-debug 4 "US" n @(:summary-atom n) (summarize n))
  (set-summary! n (summarize n))#_(reset! (:summary-atom n) (summarize n)))

(defn- update-summary-inc?! [n]
  (when-let [old   (summary n)]
    (let [new (update-summary! n)]
      (not (summary/>= old new 0)))))

;; Summaries at this stage can be suboptimal
(defn- update-summary-inc-subopt?! [n]
  (when-let [old   (summary n)]
    (let [new (reset! (:summary-atom n) (summarize n))]
      (not (summary/>= old new 0)))))

(defn- update-summary-dec?! [n]
  (when-let [old   (summary n)]
    (let [new (update-summary! n)]
      (not (summary/>= new old 0)))))

;; Run KLD and return any nodes whose summaries have changed.
(defn knuth-lightest-derivation! [active-nodes]
  (let [open  (IdentityHashMap.)
        all   (IdentityHashMap.)        
        q     (queues/make-fancy-tree-search-pq)
        cost  (fn [n] (let [s (summary n)] [(- (summary/max-reward s))
                                            (- (summary/status-val (summary/status s)))]))]
;   (println active-nodes)
    (doseq [n active-nodes]
      (.put all n (summary n))
      #_ (reset! (:summary-atom n) summary/+worst-simple-summary+)
      (set-summary! n summary/+worst-simple-summary+))
    (doseq [n (keys all)]
      (when (update-summary-inc-subopt?! n)
        (.put open n true)
        (queues/pq-add! q n (cost n))))
    (while (not (queues/pq-empty? q)) ;; Can short circuit on dead too.
      (let [n (queues/pq-remove-min! q)]
        (.remove all n)
        (doseq [p (parent-nodes n)]
          (when (.containsKey all p)
            (when (update-summary-inc?! p)
              (if (.containsKey open p)
                (queues/pq-remove! q p)
                (.put open p true))
              (queues/pq-add! q p (cost p)))))))))

;; Find and locally update all nodes that need updating
;; Return a conservative estimate of nodes that may be in cycles
;; TODO: add cycle checking.
(defn update-and-find-cycles! [active-nodes]
  (let [active-set (IdentityHashMap.)
        chase      (fn chase [n]
                     (when-not (.containsKey active-set n)
                       (when (update-summary-dec?! n)
                         (.put active-set n true)
                         (doseq [p (parent-nodes n)]
                           (chase p)))))]
    (doseq [n active-nodes]
      (chase n))
    (keys active-set)))


;; Summaries of nodes may have decreased.  Propagate these changes upwards
;; using a version of KLD, which can properly handle cycles without infinite
;; loops, or the inefficiencies of an algorithm like LDFS.
;; Algorithm: repeatedly find costs of active set using KLD, assuming
;; all nodes out of active set are fixed, then expand active set to
;; incorporate any new nodes that may change given the new updates.
(defn summaries-decreased! [nodes]
  (when-let [cycle-nodes (update-and-find-cycles! nodes)]
    (knuth-lightest-derivation! cycle-nodes)))


(comment
 (defn add-bound! [n b]
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

 (defn summary-decreased! [n]
   (util/print-debug 4 "SI" n)
   (let [cache (:summary-atom n)]
     (when-let [old @cache]
       (assert (summary/>= old (update-summary! n) 0)))))

 (defn summary-increased! [n]
   (util/print-debug 4 "SI" n)
   (let [cache (:summary-atom n)]
     (when-let [old @cache]
       (when (summary/>= (update-summary! n) old 0)
         (doseq [p (doall (parent-nodes n))]
           (summary-increased! p)))))))




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
            (let [c (consistent-choice-fn (filter (comp summary/live? summary summary/source) kids))]
              (ldfs! (summary/source c) consistent-choice-fn (summary/max-reward c) op!-fn)))
          (update-summary! root)
          (when (summary/live? (summary root))
            (recur root consistent-choice-fn bound op!-fn))))))
