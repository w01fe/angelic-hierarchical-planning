(ns angelic.search.summary
  (:refer-clojure :exclude [min max >= + ])
  (:require [edu.berkeley.ai.util :as util])
  (:import [java.util ArrayList]))

;; Summaries are essentially sufficient statistics for searches.
;; The basic idea here is to separate these statistics and their
;; propagation and caching from the underlying search space.

;; By default, a Summary must support at least an upper reward bound,
;; a status -- :live, :blocked, :solved, and sources -- an
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

;; TODO: re-source and re-child can go away.
(defprotocol Summary
  (max-reward       [s] "Admissible reward bound")
  (status           [s] "Status: :blocked, :solved, or :live")
  (source           [s] "Object being directly summarized")
  (children         [s] "Child summaries that went into this, if applicable")

  (re-source [s src bound stat-bound] "Create a new summary with same status, bounded, src, children [s]")
  (re-child [s new-children]          "Change children.")
  (eq  [s other] "equaltiy, just based on reward and status.")
  (>=  [s other] [s other bound])
  (+   [s other new-src] [s other new-src bound]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Properties ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 

(defn status-val [s]
  (cond (identical? :live s) 0
        (identical? :blocked s) 1
        (identical? :solved s) 2))

(def statuses [ :live :blocked :solved])
(def statuses-set (set statuses))

(defn live?    [s] (= (status s) :live))
;(defn stale?   [s] (= (status s) :stale))
(defn blocked? [s] (= (status s) :blocked))
;(defn dead?    [s] (not (live? s)))
(defn solved?  [s] (= (status s) :solved))

(defn viable? [summary]
  (> (max-reward summary) Double/NEGATIVE_INFINITY))

;; TODO: Is this the right stat semantics?
(defn refinable? [summary summary-bound]
  (and (live? summary) (>= summary summary-bound)))

(defn default->= [s1 s2]
  (let [r1 (max-reward s1) r2 (max-reward s2)]
    (or (> r1 r2)
        (and (= r1 r2)
             (clojure.core/>= (status-val (status s1))
                              (status-val (status s2)))))))

(defn default->=-b [s1 s2 bound]
  (let [r1 (clojure.core/min bound (max-reward s1)) r2 (clojure.core/min bound (max-reward s2))]
    (or (> r1 r2)
        (and (= r1 r2)
             (clojure.core/>= (status-val (status s1))
                              (status-val (status s2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord SimpleSummary [max-rew stat src chldren]
  Summary
  (max-reward       [s] max-rew)
  (status           [s] stat)
  (source          [s] src)
  (children        [s] chldren)
  (re-source       [s new-src bound stat-bound]
    (when (solved? s) (assert (clojure.core/>= bound (max-reward s))))
    (SimpleSummary. (clojure.core/min max-rew bound) (min-key status-val stat stat-bound) new-src [s]))
  (re-child        [s new-children] (SimpleSummary. max-rew stat src new-children))
  (eq               [s other] (and (= max-rew (max-reward other)) (= stat (status other))))
  (>=               [s other] (default->= s other))
  (>=               [s other bound] (default->=-b s other bound))
  (+ [s other src] (+ s other src Double/POSITIVE_INFINITY))
  (+                [s other new-src bound]
    (SimpleSummary.
     (clojure.core/min (clojure.core/+ max-rew (max-reward other)) bound)
     (min-key status-val stat (status other))
     new-src [s other])))

(defn make-live-simple-summary [max-reward source] (SimpleSummary. max-reward :live source nil))
(defn make-blocked-simple-summary [max-reward source] (SimpleSummary. max-reward :blocked source nil))
;(defn make-stale-simple-summary [max-reward source] (SimpleSummary. max-reward :stale [source]))
(defn make-solved-simple-summary [max-reward source] (SimpleSummary. max-reward :solved source nil))

(defn make-simple-summary [max-reward status source]
  (util/assert-is (contains? statuses-set status))
  (assert source)
  (SimpleSummary. max-reward status source nil))

(comment
  (defn go-stale [summary]
   (assert (= (status summary) :live))
   (make-stale-simple-summary (max-reward summary) (util/safe-singleton (sources summary)))))

(def +worst-simple-summary+ (make-blocked-simple-summary Double/NEGATIVE_INFINITY :worst))
(def +best-simple-summary+  (make-live-simple-summary Double/POSITIVE_INFINITY :best)) ;; don't be too optimistic
(def +zero-simple-summary+  (SimpleSummary. 0 :solved nil nil))

(defn simple-summary-str [s] (str "Summary:" (max-reward s) (status s) #_ (vec (:opt-sol s))))
(defmethod print-method SimpleSummary [s o] (print-method (simple-summary-str s) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; IntervalSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn is-vec [is] [(:min-rew is Double/NEGATIVE_INFINITY) #_ (max-reward is) (status-val (status is))])


(defrecord IntervalSummary [min-rew max-rew stat src chldren]
  Summary
  (max-reward       [s] max-rew)
  (status           [s] stat)
  (source           [s] src)
  (children         [s] chldren)
  (re-source        [s new-src bound stat-bound] (throw (RuntimeException.))) ;; TODO: needed!
  (re-child         [s new-children] (throw (RuntimeException.)))
  (+                [s other src] (throw (RuntimeException.)))
  (eq               [s other] (= (is-vec s) (is-vec other)))
  (>=               [s other] (not (neg? (compare (is-vec s) (is-vec other)))))
  (+                [s other new-src bound]
   (IntervalSummary.
     (clojure.core/min (clojure.core/+ min-rew (:min-rew other Double/NEGATIVE_INFINITY)) bound)                     
     (clojure.core/min (clojure.core/+ max-rew (max-reward other)) bound)
     (min-key status-val stat (status other))
     new-src [s other])))

(defn make-interval-summary [min-reward max-reward status source]
  (util/assert-is (contains? statuses-set status))
  (IntervalSummary. min-reward max-reward status source nil))


(defn iv-summary-str [s] (str "IVSum:" [(:min-rew s) (max-reward s)] (status s)))
(defmethod print-method IntervalSummary [s o] (print-method (iv-summary-str s) o))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn- max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

;; TODO: can we safely handle empty case here?
(defn apply-max [stats]
  (if-let [stats (seq stats)]
   (loop [best (first stats) stats (next stats)]
     (if stats
       (recur (if (>= (first stats) best) (first stats) best) (next stats))
       best))
   +worst-simple-summary+))
(defn max [& stats] (apply-max stats)
  #_(apply max-compare >= (cons +worst-simple-summary+ stats)))

;; Note: this doesn't account for interaction between max and bound...
(defn or-combine [summaries new-src bound]
  (let [best (apply-max summaries)]
    (re-source best new-src bound :solved)))


(defn apply-max-b [stats bound]
  (if-let [stats (seq stats)]
   (loop [best (first stats) stats (next stats)]
     (if stats
       (recur (if (>= (first stats) best bound) (first stats) best) (next stats))
       best))
       +worst-simple-summary+))

;; This version takes bound into account
(defn or-combine-b [summaries new-src bound]
  (let [best (apply-max-b summaries bound)]
    (re-source best new-src bound :solved)))

(defn liven [summary new-src]
  (re-source summary new-src Double/POSITIVE_INFINITY :live))


(defn min [& stats] (apply max-compare (complement >=) (cons +best-simple-summary+ stats)))
;(defn sum [& stats] (if (empty? stats) +zero-simple-summary+ (reduce + (first stats) (next stats))))

(defn bound [summary reward-bound]
   (re-source summary (source summary) reward-bound :solved))

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

(defn extract-leaf-source-seq [summary]
  (map source (extract-leaf-seq summary)))

(defn extract-single-leaf [summary stop?-fn]
  (util/safe-singleton (extract-leaf-seq summary stop?-fn)))



(defn extract-solution-pair [summary action-extractor]
  (assert (solved? summary))
  [(filter identity (map action-extractor (extract-leaf-source-seq summary)))
   (max-reward summary)])

(def *last-solution* nil)

(defn solve [summary-fn expand!-fn action-extractor]
  (loop []
    (let [summary (summary-fn)]
      (util/print-debug 1 "next round: " summary (Thread/sleep 10))
      (cond (solved? summary) (do (def *last-solution* summary)
                                  (extract-solution-pair summary action-extractor))
            (= (max-reward summary) Double/NEGATIVE_INFINITY) nil
            :else (do (expand!-fn summary)
                      (recur))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Misc. Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
       [best-thing best-summary rest-things rest-summary])))


  (defmacro assert-valid-summary-change
    ([old-summary new-summary] ( assert-valid-summary-change old-summary new-summary ""))
    ([old-summary new-summary msg]
       `(do (util/assert-is (<= (max-reward ~new-summary) (max-reward ~old-summary)) "%s" [~old-summary ~new-summary ~msg])
            (when-not (live? ~old-summary) (assert (= ~old-summary ~new-summary)))))))

