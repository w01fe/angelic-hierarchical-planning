(ns angelic.search.summary
  (:refer-clojure :exclude [min max >= + ])
  (:require [edu.berkeley.ai.util :as util]))

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

(defprotocol Summary
  (max-reward       [s] "Admissible reward bound")
  (status           [s] "Status: :blocked, :solved, or :live")
  (source           [s] "Object being directly summarized")
  (children         [s] "Child summaries that went into this, if applicable")

  (re-source [s src bound stat-bound] "Create a new summary with same status, bounded, src, children [s]")
  (re-child [s new-children]          "Change children.")
  (eq  [s other] "equaltiy, just based on reward and status.")
  (>=  [s other])
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
    (SimpleSummary. (clojure.core/min max-rew bound) (min-key status-val stat stat-bound) new-src [s]))
  (re-child        [s new-children] (SimpleSummary. max-rew stat src new-children))
  (eq               [s other] (and (= max-rew (max-reward other)) (= stat (status other))))
  (>=               [s other] (default->= s other))
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

(defn or-combine [summaries new-src bound]
  (let [best (apply-max summaries)]
    (re-source best new-src bound :solved)))

(defn liven [summary new-src]
  (re-source summary new-src Double/POSITIVE_INFINITY :live))


(defn min [& stats] (apply max-compare (complement >=) (cons +best-simple-summary+ stats)))
;(defn sum [& stats] (if (empty? stats) +zero-simple-summary+ (reduce + (first stats) (next stats))))

(comment
 (defn bound [summary reward-bound]
   (re-source summary #(clojure.core/min % reward-bound))))

(defn extract-leaf-seq
  ([summary] (extract-leaf-seq summary (comp empty? children)))
  ([summary stop?-fn]  
     (if (stop?-fn summary)
       [summary]
       (apply concat (map #(extract-leaf-seq % stop?-fn) (children summary))))))

(defn extract-leaf-source-seq [summary] (map source (extract-leaf-seq summary)))

(defn extract-single-leaf [summary stop?-fn]
  (util/safe-singleton (extract-leaf-seq summary stop?-fn)))


(defn extract-source-seq [summary]
 ;(when (source summary) (println (angelic.search.implicit.subproblem-eval/subproblem-name (source summary))))
;  (println "." summary)
  (if-let [kids (seq (children summary))]
    (apply concat (map extract-source-seq kids))
    [(util/make-safe (source summary) "%s" (class summary))]))

(defn extract-solution-pair [summary action-extractor]
  (assert (solved? summary))
  [(filter identity (map action-extractor (extract-source-seq summary)))
   (max-reward summary)])

(def *last-solution* nil)

(defn solve [summary-fn expand!-fn action-extractor]
  (loop []
    (let [summary (summary-fn)]
      (util/print-debug 1 "next round: " summary (Thread/sleep 1))
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

