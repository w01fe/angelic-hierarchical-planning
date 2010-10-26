(ns angelic.search.incremental.summary
  (:refer-clojure :exclude [min max >= +])
  (:require [edu.berkeley.ai.util :as util]))

;; Summaries are essentially sufficient statistics for searches.
;; The basic idea here is to separate these statistics and their
;; propagation and caching from the underlying search space.

;; By default, a Summary must support at least an upper reward bound,
;; a status -- :live, :blocked, or :solved, and sources -- an
;; ordered list of source nodes.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Summary
  (max-reward       [s] "Admissible reward bound")
  (status           [s] "Status: :blocked, :solved, or :live")
  (sources          [s] "Nil or optimal solution, if solved")

  (>=  [s other])
  (+   [s other]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Properties ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 
(defn status-val [s]
  (case s
        :live    0
        :blocked 1
        :solved  2))

(def statuses [:live :blocked :solved])

(defn live?    [s] (= (status s) :live))
(defn blocked? [s] (= (status s) :blocked))
(defn solved?  [s] (= (status s) :solved))

(defn viable? [summary]
  (> (max-reward summary) Double/NEGATIVE_INFINITY))

;; TODO: Is this the right stat semantics?
(defn refinable? [summary summary-bound]
  (and (live? summary) (>= summary summary-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Combinations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn default->= [s1 s2]
  (let [r1 (max-reward s1) r2 (max-reward s2)]
    (or (> r1 r2)
        (and (= r1 r2)
             (clojure.core/>= (status-val (:status s1))
                              (status-val (:status s2)))))))

(defn- max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

;; TODO: can we safely handle empty case here?
(defn max [& stats] (apply max-compare >= stats))
(defn min [& stats] (apply max-compare (complement >=) stats))
;(defn sum [& stats] )


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
       [best-thing best-summary rest-things rest-summary]))))


(defmacro assert-valid-summary-change
  ([old-summary new-summary] ( assert-valid-summary-change old-summary new-summary ""))
  ([old-summary new-summary msg]
     `(do (util/assert-is (<= (max-reward ~new-summary) (max-reward ~old-summary)) "%s" [~old-summary ~new-summary ~msg])
        (when-not (live? ~old-summary) (assert (= ~old-summary ~new-summary))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SimpleSummary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord SimpleSummary [max-rew stat srcs]
  Summary
  (max-reward       [s] max-rew)
  (status           [s] stat)
  (sources          [s] srcs)
  (>=               [s other] (default->= s other))
  (+                [s other]
    (SimpleSummary.
     (clojure.core/+ max-rew (max-reward other))
     (min-key status-val stat (status other))
     (concat srcs (sources other)))))

(defn make-live-simple-summary [max-reward source] (SimpleSummary. max-reward :live [source]))
(defn make-blocked-simple-summary [max-reward source] (SimpleSummary. max-reward :blocked [source]))
(defn make-solved-simple-summary [max-reward source] (SimpleSummary. max-reward :solved [source]))

(def +worst-simple-summary+ (make-blocked-summary is/neg-inf :worst))
(def +best-simple-summary+  (make-live-summary is/pos-inf) :best) ;; don't be too optimistic
(def +zero-simple-summary+  (SimpleSummary. 0 :solved []))

(defn summary-str [s] (str "Summary:" (max-reward s) (status s) #_ (vec (:opt-sol s))))
(defmethod print-method SimpleSummary [s o] (print-method (summary-str s) o))
