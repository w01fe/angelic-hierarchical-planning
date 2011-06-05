(ns angelic.search.summary
  (:refer-clojure :exclude [>= + ])
  (:require [angelic.util :as util])
  (:import [java.util ArrayList]))

;; Summaries are essentially sufficient statistics for searches.
;; The basic idea here is to separate these statistics and their
;; propagation and caching from the underlying search space.

;; By default, a Summary must support at least an upper reward bound,
;; a status -- :live, :blocked, or :solved, and sources -- an
;; ordered list of source nodes.

;; We assume :solved > :blocked > :live , since this is the order
;; that we actually want plans to appear at the top-level.
;; BUT, note that this can lead to apparent INCREASES in summary,
;; as a plan goes from, e.g., live to solved.

;; TODO: this could be fixed by separating opt and pess summaries ?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Summary
  (max-reward       [s] "Admissible reward bound, or nil")
  (reward           [s] "Type-dependent reward")
  (status           [s] "Status: :blocked, :solved, or :live")
  (source           [s] "Object being directly summarized")
  (children         [s] "Child summaries that went into this, if applicable")
  (leafen           [s bound new-stat new-src] "Make status live, cut off children.")
  (re-source [s src bound stat-bound] "Create a new summary with same status.")
  (eq  [s other]                      "equaltiy, just based on reward and status.")
  (>=  [s other bound]                "Greater, under specified bound?")
  (+   [s other new-src bound]        "Add summaries and apply bound."))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Derived fns ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 

(defn status-val [s]
  (cond (identical? :live s) 0
        (identical? :blocked s) 1
        (identical? :solved s) 2))

(def statuses [ :live :blocked :solved])
(def statuses-set (set statuses))

(defn live?    [s] (= (status s) :live))
(defn blocked? [s] (= (status s) :blocked))
(defn solved?  [s] (= (status s) :solved))

(def neg-inf Double/NEGATIVE_INFINITY)
(declare +worst-simple-summary+)

(defn viable? [summary] (> (max-reward summary) neg-inf))

;; TODO: can we safely handle empty case here?
(defn apply-max-b [stats bound]
  (if-let [stats (seq stats)]
   (loop [best (first stats) stats (next stats)]
     (if stats
       (recur (if (>= (first stats) best bound) (first stats) best) (next stats))
       best))
   +worst-simple-summary+))

(defn eps-bound [x] (clojure.core/+ 0.000000001 x))

(defn or-combine-b [summaries new-src bound]
  (let [best (apply-max-b summaries bound)]
    (when (solved? best) (util/assert-is (clojure.core/>= (eps-bound bound) (max-reward best)) "%s" [new-src (def *bad* new-src)]))
    (re-source best new-src bound :solved)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simple search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn extract-leaf-seq
  ([summary] (extract-leaf-seq summary (comp empty? children)))
  ([summary stop?-fn]
     (let [l   (ArrayList.) ;; functional version slow for some reason...
           dfs (fn dfs [s]
                 (if (stop?-fn s)
                   (.add l s)
                   (doseq [c (children s)] (dfs c))))]
       (dfs summary)
       (seq l))))

(defn extract-solution-pair [summary action-extractor]
  (assert (solved? summary))
  [(keep (comp action-extractor source) (extract-leaf-seq summary))
   (reward summary)])

(declare *last-solution*)

(defn solve [summary-fn expand!-fn action-extractor]
  (loop []
    (let [summary (summary-fn)]
      (util/print-debug 1 "next round: " summary (Thread/sleep 10))
      (cond (solved? summary) (do (def *last-solution* summary)
                                  (extract-solution-pair summary action-extractor))
            (viable? summary) (do (expand!-fn summary) (recur))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple summary, with upper reward bound only

(defrecord SimpleSummary [max-rew stat src chldren]
  Summary
  (max-reward       [s] max-rew)
  (reward           [s] max-rew)
  (status           [s] stat)
  (source          [s] src)
  (children        [s] chldren)
  (leafen           [s bound new-stat new-src] (SimpleSummary. (min bound max-rew) new-stat new-src nil))
  (re-source       [s new-src bound stat-bound]
    (when (solved? s) (assert (clojure.core/>= (eps-bound bound) max-rew)))
    (SimpleSummary. (min max-rew bound) (min-key status-val stat stat-bound) new-src [s]))
  (eq               [s other] (and (= max-rew (max-reward other)) (= stat (status other))))
  (>=               [s1 s2 bound]
    (let [r1 (min bound (max-reward s1)) r2 (min bound (max-reward s2))]
      (or (> r1 r2)
          (and (= r1 r2)
               (clojure.core/>= (status-val (status s1))
                                (status-val (status s2)))))))
  (+                [s other new-src bound]
    (let [new-stat (min-key status-val stat (status other))
	  r        (clojure.core/+ max-rew (max-reward other))]
      (when (= new-stat :solved) (assert (clojure.core/>= bound r)))      
      (SimpleSummary. (min r bound) new-stat new-src [s other]))))

(defn make-live-simple-summary [max-reward source] (SimpleSummary. max-reward :live source nil))
(defn make-blocked-simple-summary [max-reward source] (SimpleSummary. max-reward :blocked source nil))
(defn make-solved-simple-summary [max-reward source] (SimpleSummary. max-reward :solved source nil))

(defn make-simple-summary [max-reward status source]
  (util/assert-is (contains? statuses-set status))
  (assert source)
  (SimpleSummary. max-reward status source nil))

(def +worst-simple-summary+ (make-blocked-simple-summary neg-inf :worst))

(defn simple-summary-str [s] (str "Summary:" (max-reward s) (status s) #_ (vec (:opt-sol s))))
(defmethod print-method SimpleSummary [s o] (print-method (simple-summary-str s) o))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleWeightedSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Weighted A* summary, without pessimistic descriptions.
;; TODO: bound can come from above .. .. . . .. . . . (wrong weight assigned...)
;; note: tie-breaking is important -- generally, later is better in dash-astar

(declare make-simple-weighted-summary*)

(defn sws-vec [sws] [(:wtd-rew sws) (status-val (:stat sws)) (:max-rew sws) (:max-gap sws)]) ;; TODO: remove max-gap?
(defn bounded-f [sws wt ub]
  (cond (clojure.core/>= ub (:max-rew sws)) (:wtd-rew sws)
        (zero? (:max-rew sws)) (* wt ub)
        :else                  (min ub (* (:wtd-rew sws) (/ ub (:max-rew sws)))))) ;; for rounding...
(defn bounded-sws-vec [sws wt ub] [(bounded-f sws wt ub) (:max-rew sws) (status-val (:stat sws))])

(defrecord SimpleWeightedSummary [wtd-rew max-rew max-gap stat src chldren]
  Summary
  (max-reward       [s] max-rew)
  (reward           [s] wtd-rew)
  (status           [s] stat)
  (source          [s] src)
  (children        [s] chldren)
  (leafen           [s bound new-stat new-src] (SimpleWeightedSummary. (if (< bound max-rew) (min bound (* wtd-rew (/ bound max-rew))) wtd-rew) (min bound max-rew) max-gap new-stat new-src nil))  
  (re-source       [s new-src bound stat-bound] (make-simple-weighted-summary* wtd-rew max-rew max-gap stat new-src [s])) ;;Needed for single-sum; todo: bound?
  (eq               [s other] (= (sws-vec s) (sws-vec other)))
  (>=               [s1 s2 bound] (not (neg? (compare (sws-vec s1) (sws-vec s2))))) ;; TODO: bound?
  (+                [s other new-src bound] ;; ignore bound for now
    (make-simple-weighted-summary* 
     (clojure.core/+ wtd-rew (:wtd-rew other))
     (clojure.core/+ max-rew (:max-rew other))
     (max (:max-gap s) (:max-gap other))
     (min-key status-val stat (:stat other))
     new-src [s other])))

(defn make-simple-weighted-summary* [wtd-rew max-rew max-gap stat src chldren]
  (util/assert-is (<= wtd-rew max-rew) "%s" [ stat src chldren])
  (util/assert-is (contains? statuses-set stat))
  (SimpleWeightedSummary. wtd-rew max-rew (min max-gap (- max-rew wtd-rew)) stat src chldren))

(defn make-simple-weighted-summary [max-reward weight status source]
  (make-simple-weighted-summary*  (* max-reward weight) max-reward (* max-reward (- 1 weight)) status source nil))

(defmethod print-method SimpleWeightedSummary [s o]
 (print-method (str "SWS:" (:wtd-rew s) " " (max-reward s) " " (:max-gap s) " " (status s)) o))

(defn make-sws-or-combiner [weight]
  (fn or-combine-sws [summaries new-src ub]
    (if (empty? summaries)
      (make-simple-weighted-summary neg-inf 1 :blocked new-src)
     (let [or-bound (reduce max (map :max-rew summaries))]
       (loop [best (first summaries) summaries (next summaries)]
         (if summaries
           (recur (if (pos? (compare (bounded-sws-vec best weight ub) (bounded-sws-vec (first summaries) weight ub))) best (first summaries))
                  (next summaries))
           (make-simple-weighted-summary* (bounded-f best weight ub) (min or-bound ub) (:max-gap best) (status best) new-src [best])))))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; BoundedWeightedSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bounded weighted summary, with reward = max(opt * weight, pess)
;; Although not strictly necessary, keep track of best pess reward and use to bound.

;; TODO: safe way to take bounds into account
;; TODO: way to prevent blocked even when (worse) live option is available ?
;; TODO: lower-bounding is not correct for subproblems; they get worse as they release children...
;;    this leads to infinite loops ieven in easy problems, e.g., nav switch.
;; TODO: do not release children until at least one achieves the previous bound?

(declare make-bw-summary*)

(defrecord BoundedWeightedSummary [wt p-val w-val o-val max-gap stat src
                                   p-children w-children o-children]
  Summary
  (max-reward       [s] o-val)
  (reward           [s] w-val) 
  (status           [s] stat)
  (source           [s] src)
  (children         [s] o-children)
  (re-source        [s new-src bound stat-bound] (throw (RuntimeException.)))  
  (eq               [s other]
    (let [rel-keys [#_ :p-val #_ :w-val :o-val :stat]]
      (= (map #(% s) rel-keys) (map #(% other) rel-keys))))
  (>=               [s other bound]  ;; TODO: bound ???  
    (or (> (min bound o-val) (min bound (:o-val other)))
        (and (= (min bound o-val) (min bound (:o-val other)))
             (clojure.core/>= (status-val stat) (status-val (status other))))))
  (+                [s other new-src bound] 
   (let [p-sum (clojure.core/+ p-val (:p-val other))
         w-sum (clojure.core/+ w-val (:w-val other))
         o-sum (min (clojure.core/+ o-val (:o-val other)) bound)]
     (assert (<= p-sum o-sum))
     (make-bw-summary*
      wt p-sum w-sum o-sum
      (max max-gap (:max-gap other))
      (min-key status-val stat (status other))
      new-src [s other] [s other] [s other]))))

(defn- make-bw-summary* [wt p-val f-val o-val max-gap status source
                         p-children w-children o-children]
  (let [final-f (min (max p-val f-val (* wt o-val)) o-val)]
    (util/assert-is (<= p-val final-f o-val) "%s" [source children])
    (BoundedWeightedSummary. wt p-val final-f o-val (min max-gap (- o-val p-val))
                             status source p-children w-children o-children)))

(defn make-bw-summary [wt p-val o-val status source]
  (util/assert-is (contains? statuses-set status))
  (make-bw-summary* wt p-val (max p-val (* o-val wt)) o-val
                    (- o-val p-val) status source nil nil nil))

;(defn bw-summary? [s] (instance? SimpleWeightedSummary s))
(defmethod print-method BoundedWeightedSummary [s o]
  (print-method (pr-str "<BWSum:" [(:p-val s) (:w-val s) (:o-val s)]
                        (:max-gap s) (status s) ">")
                o))

(def worst-bws (make-bw-summary 1 neg-inf neg-inf :blocked :dummy ))

;; TODO: ignoring upper bounds and
;; possibility of keeping lower bounds (see below) for now.
;; Warning, this semantics may hide :blocked issues.

(defn apply-max-ge [ge s]
  (assert (seq s))
  (loop [best (first s) s (next s)]
    (if s
      (recur (if (ge (first s) best) (first s) best) (next s))
      best)))

(defn better-bws
  ([k] (better-bws k Double/POSITIVE_INFINITY))
  ([k b]
     (fn [b1 b2]
       (cond #_ (and (not (= :blocked (status b1))) (= :blocked (status b2)))
             #_ true

             #_ (and (= :blocked (status b1)) (not (= :blocked (status b2))))
             #_ false

             (> (min (k b1) b) (min (k b2) b))
             true

             (< (min (k b1) b) (min (k b2) b))
             false

             :else
             (clojure.core/>= (status-val (status b1)) (status-val (status b2)))))))

(defn or-combine-bws [summaries new-src bound]
  (if (empty? summaries)
    worst-bws
   (let [best-p (apply-max-ge (better-bws :p-val) summaries)
         best-w (apply-max-ge (better-bws :w-val) summaries)
         best-o (apply-max-ge (better-bws :o-val) summaries)]
     (make-bw-summary*
      (:wt (first summaries))
      (:p-val best-p) (:w-val best-w) (min (:o-val best-o) bound)
      (:max-gap best-o) (:stat best-o) new-src
      [best-p] [best-w] [best-o]))))






(comment ;; Even more broken?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleWeightedSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple weighted summary, with reward = max(opt * weight, pess)
;; TODO: add alpha, to scale weights?
;; Although not strictly necessary, keep track of best pess reward and use to bound.
;; Note: we cannot propagate upper bounds in the presence of shared pessimistic
;; problems, since they might be lower bounds for totally different input sources.
;; I.e., suppose we have empty pessimistic set.  Subsumed by every optimistic, incl.
;;  empty set.

;; TODO: something smarter with max-gap for -inf pess.
;; TODO: safe way to take bounds into account
;; TODO: way to prevent blocked even when (worse) live option is available ?
;; TODO: lower-bounding is not correct for subproblems; they get worse as they release children...
;;    this leads to infinite loops ieven in easy problems, e.g., nav switch.
;; TODO: do not release children until at least one achieves the previous bound?

;; TODO: this handling of o-val probably isn't right either ...

(declare *sws-weight*) ; Weight, >= 1.

(declare make-sw-summary* sw-summary?)
(defn sws-vec [is] [(:f-val is neg-inf) (status-val (status is)) (:p-val is neg-inf) (:o-val is)])

;; Note: o-val is a local upper bound, not nec. a valid global UB.
;; Idea: when we lift up into a pair, that's when we patch up...
;; (can be needed elsewhere, anytime we pop out of decomposition)?
(defrecord SimpleWeightedSummary [p-val f-val o-val max-gap stat src chldren]
  Summary
  (max-reward       [s] nil)
  (reward           [s] f-val) 
  (status           [s] stat)
  (source           [s] src)
  (children         [s] chldren)
  (re-source        [s new-src bound stat-bound] (throw (RuntimeException.)))  
  (eq               [s other] (= (sws-vec s) (sws-vec other)))
  (>=               [s other bound] (not (neg? (compare (sws-vec s) (sws-vec other))))) ;; TODO: bound ???  
  (+                [s other new-src bound]
   (util/assert-is (sw-summary? other))
   (let [p-sum (clojure.core/+ p-val (:p-val other))
         f-sum (clojure.core/+ f-val (:f-val other))]
     (make-sw-summary*
      p-sum (min (max f-sum (* *sws-weight* bound)) bound) bound  ;; TODO?
      (max max-gap (:max-gap other)) 
      (min-key status-val stat (status other))
      new-src [s other]))))

(defn- make-sw-summary* [p-val f-val o-val max-gap status source children]
  (util/assert-is (<= p-val f-val o-val) "%s" [source children])
  (SimpleWeightedSummary. p-val f-val o-val (min max-gap (- o-val p-val)) status source children))

(defn make-sw-summary [p-val o-val status source children]
  (util/assert-is (contains? statuses-set status))
  (let [f-val (max p-val (* o-val *sws-weight*))]
    (make-sw-summary* p-val f-val o-val (- o-val p-val) status source children)))

(defn sw-summary? [s] (instance? SimpleWeightedSummary s))
(defmethod print-method SimpleWeightedSummary [s o]
  (print-method (str "SWSum:" [(:p-val s) (:f-val s) (:o-val s) (:max-gap s)] (status s)) o))

;(def +worst-sw-summary+ (make-sw-summary* neg-inf neg-inf neg-inf 0 :blocked :worst-sw nil))

;; Can-cache-fn? tells us whether it's safe to use cached lower bounds...
;; TODO: now this is almost just usual OR ...
(defn make-sws-or-combiner [init-lb can-cache?-fn]
  (let [p-atom (atom (or init-lb neg-inf))]
    (fn or-combine-sws [summaries new-src ub]
      (assert (seq summaries))
      (let [lb (reduce max (map :p-val summaries))
            lb (if (can-cache?-fn new-src) (swap! p-atom max lb) lb)
            bounded-f #(min (:o-val %) (max lb (:f-val %)))
            sws-lb-vec #(vector (bounded-f %) (status-val (status %)) (:p-val %))
            ]
        (loop [best (first summaries) summaries (next summaries)]
          (if summaries
            (recur (if (not (neg? (compare (sws-lb-vec best) (sws-lb-vec (first summaries))))) best (first summaries))
                   (next summaries))
            (make-sw-summary* (min (:o-val best) lb)
                              (bounded-f best)
                              (:o-val best)
                              (:max-gap best) (status best) new-src [best])))))))



  )


(comment
  ;; Possibly-broken version (with decomposition) -- propagates potentially invalid upper bounds.

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleWeightedSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple weighted summary, with reward = max(opt * weight, pess)
;; TODO: add alpha, to scale weights?
;; Although not strictly necessary, keep track of best pess reward and use to bound.
;; Note: we cannot propagate upper bounds in the presence of shared pessimistic
;; problems, since they might be lower bounds for totally different input sources.
;; I.e., suppose we have empty pessimistic set.  Subsumed by every optimistic, incl.
;;  empty set.


(declare *sws-weight*) ; Weight, >= 1.

(declare make-sw-summary* sw-summary?)
(defn sws-vec [is] [(:f-val is neg-inf) (status-val (status is)) (:p-val is neg-inf)])

;; Try to bound withotu losing component f-val -- a bit hacky...
(defn bounded-sw-f-val
  ([sws lb ub] (bounded-sw-f-val (:p-val sws) (:f-val sws) (:o-val sws) lb ub) #_ (util/prln  (bounded-sw-f-val (:p-val sws) (:f-val sws) (:o-val sws) lb ub) sws lb ub))
  ([p-val f-val o-val lb ub]
     (util/assert-is (<= p-val f-val o-val))
     (util/assert-is (<= lb ub))
     (util/assert-is (<= p-val ub))
     (max (min o-val lb) p-val
      (* *sws-weight* (min o-val ub))
      (if (< ub o-val)
        (if (zero? o-val) neg-inf (min ub (* f-val (/ ub o-val))))
        f-val))))

(defrecord SimpleWeightedSummary [p-val f-val o-val max-gap stat src chldren]
  Summary
  (max-reward       [s] o-val)
  (reward           [s] f-val) 
  (status           [s] stat)
  (source           [s] src)
  (children         [s] chldren)
  (re-source        [s new-src bound stat-bound] (throw (RuntimeException.)))  
  (eq               [s other] (= (sws-vec s) (sws-vec other)))
  (>=               [s other bound] (not (neg? (compare (sws-vec s) (sws-vec other))))) ;; TODO: bound ???  
  (+                [s other new-src bound]
   (util/assert-is (sw-summary? other))
   (let [p-sum (clojure.core/+ p-val (:p-val other))
         f-sum (clojure.core/+ f-val (:f-val other))
         o-sum (clojure.core/+ o-val (:o-val other))]
     (make-sw-summary*
      p-sum (bounded-sw-f-val p-sum f-sum o-sum p-sum bound) (min bound o-sum)
      (max max-gap (:max-gap other)) 
      (min-key status-val stat (status other))
      new-src [s other]))))

(defn- make-sw-summary* [p-val f-val o-val max-gap status source children]
  (util/assert-is (<= p-val f-val o-val) "%s" [source children])
  (SimpleWeightedSummary. p-val f-val o-val (min max-gap (- o-val p-val)) status source children))

(defn make-sw-summary [p-val o-val status source children]
  (util/assert-is (contains? statuses-set status))
  (let [f-val (max p-val (* o-val *sws-weight*))]
    (make-sw-summary* p-val f-val o-val (- o-val p-val) status source children)))

(defn sw-summary? [s] (instance? SimpleWeightedSummary s))
(defmethod print-method SimpleWeightedSummary [s o]
  (print-method (str "SWSum:" [(:p-val s) (:f-val s) (:o-val s) (:max-gap s)] (status s)) o))

;(def +worst-sw-summary+ (make-sw-summary* neg-inf neg-inf neg-inf 0 :blocked :worst-sw nil))

(defn make-sws-or-combiner [init-lb]
  (let [p-atom (atom (or init-lb neg-inf))]
    (fn or-combine-sws [summaries new-src ub]
      (assert (seq summaries))
      (let [lb (reset! p-atom (reduce max (cons @p-atom (map :p-val summaries))))
            bounded-sws-vec (fn [sws] [(bounded-sw-f-val sws lb ub) (status-val (status sws)) (:p-val sws)])]
        (util/assert-is (<= lb ub) "%s" [init-lb @p-atom summaries new-src (def *bad* summaries)])
        (loop [best (first summaries) summaries (next summaries)]
          (if summaries
            (recur (if (not (neg? (compare (bounded-sws-vec best) (bounded-sws-vec (first summaries))))) best (first summaries))
                   (next summaries))
            (let [f-val (bounded-sw-f-val best lb ub)
                  o-val (min ub (:o-val best))
                  p-val (min lb o-val)]
              (make-sw-summary* p-val f-val o-val (:max-gap best) (status best) new-src [best]))))))))



)






(comment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; IntervalSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ;; Fancier summary, which maintains both lower and upper reward bounds.

 (declare make-interval-summary*)
 (defn is-id-vec [is] [(:min-rew is neg-inf) (status-val (status is))])
 (defn is-sort-vec [is] [(:min-rew is neg-inf) (max-reward is) (status-val (status is))])

 (defrecord IntervalSummary [min-rew max-rew stat src chldren]
   Summary
   (max-reward       [s] max-rew)
   (status           [s] stat)
   (source           [s] src)
   (children         [s] chldren)
   (re-source        [s new-src bound stat-bound]
                     (make-interval-summary* min-rew (min max-rew bound)
                                             (min-key status-val stat stat-bound) new-src [s]))  
   (eq               [s other] (= (is-id-vec s) (is-id-vec other)))
   (>=               [s other bound] (not (neg? (compare (is-sort-vec s) (is-sort-vec other))))) ;; TODO: bound ???  
   (+                [s other new-src bound]
                     (make-interval-summary*
                      (clojure.core/+ min-rew (:min-rew other neg-inf))
                      (min (clojure.core/+ max-rew (max-reward other)) bound)
                      (min-key status-val stat (status other))
                      new-src [s other])))

 (defn- make-interval-summary* [min-reward max-reward status source children]
   (util/assert-is (<= min-reward max-reward))
   (IntervalSummary. min-reward max-reward status source children))

 (defn make-interval-summary [min-reward max-reward status source]
   (util/assert-is (contains? statuses-set status))
   (make-interval-summary* min-reward max-reward status source nil))


 (defn interval-summary? [s] (instance? IntervalSummary s))
 (defn iv-summary-str [s] (str "IVSum:" [(:min-rew s) (max-reward s)] (status s)))
 (defmethod print-method IntervalSummary [s o] (print-method (iv-summary-str s) o)))










;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Old stuff (to delete) ;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

;(defn min [& stats] (apply max-compare (complement >=) (cons +best-simple-summary+ stats)))

;(defn sum [& stats] (if (empty? stats) +zero-simple-summary+ (reduce + (first stats) (next stats))))

(defn bound [summary reward-bound]
   (re-source summary (source summary) reward-bound :solved))

(defn liven [summary new-src]
  (re-source summary new-src Double/POSITIVE_INFINITY :live))

; (defn max [& stats] (apply-max stats))

(defn apply-max [stats]
  (if-let [stats (seq stats)]
   (loop [best (first stats) stats (next stats)]
     (if stats
       (recur (if (>= (first stats) best 0) (first stats) best) (next stats))
       best))
   +worst-simple-summary+))

;; Note: this doesn't account for interaction between max and bound...
(defn or-combine [summaries new-src bound]
  (let [best (apply-max summaries)]
    (re-source best new-src bound :solved)))

;(def +best-simple-summary+  (make-live-simple-summary Double/POSITIVE_INFINITY :best)) ;; don't be too optimistic
;(def +zero-simple-summary+  (SimpleSummary. 0 :solved nil nil))

;(defn refinable? [summary summary-bound]
;(and (live? summary) (>= summary summary-bound)))
