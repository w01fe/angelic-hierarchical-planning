(ns angelic.search.summary
  (:refer-clojure :exclude [min max >= + ])
  (:require [edu.berkeley.ai.util :as util])
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

(defn viable? [summary] (> (reward summary) neg-inf))

;; TODO: can we safely handle empty case here?
(defn apply-max-b [stats bound]
  (if-let [stats (seq stats)]
   (loop [best (first stats) stats (next stats)]
     (if stats
       (recur (if (>= (first stats) best bound) (first stats) best) (next stats))
       best))
   +worst-simple-summary+))

(defn or-combine-b [summaries new-src bound]
  (let [best (apply-max-b summaries bound)]
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
  (re-source       [s new-src bound stat-bound]
    (when (solved? s) (assert (clojure.core/>= bound max-rew)))
    (SimpleSummary. (clojure.core/min max-rew bound) (min-key status-val stat stat-bound) new-src [s]))
  (eq               [s other] (and (= max-rew (max-reward other)) (= stat (status other))))
  (>=               [s1 s2 bound]
    (let [r1 (clojure.core/min bound (max-reward s1)) r2 (clojure.core/min bound (max-reward s2))]
      (or (> r1 r2)
          (and (= r1 r2)
               (clojure.core/>= (status-val (status s1))
                                (status-val (status s2)))))))
  (+                [s other new-src bound]
    (SimpleSummary.
     (clojure.core/min (clojure.core/+ max-rew (max-reward other)) bound)
     (min-key status-val stat (status other))
     new-src [s other])))

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

;; Simple weighted summary, with reward = max(opt * weight, pess)
;; TODO: add alpha, to scale weights?
;; TODO: how do we infer max-gap under bound ?

(declare *sws-weight*) ; Weight, >= 1.

(declare make-sw-summary* sw-summary?)
(defn sws-vec [is] [(:f-val is neg-inf) (status-val (status is)) (:min-rew is neg-inf)])

(defrecord SimpleWeightedSummary [min-rew f-val max-rew max-gap stat src chldren]
  Summary
  (max-reward       [s] nil)
  (reward           [s] f-val) 
  (status           [s] stat)
  (source           [s] src)
  (children         [s] chldren)
  (re-source        [s new-src bound stat-bound]
    (make-sw-summary* min-rew (clojure.core/min f-val bound) (clojure.core/min max-rew bound) ;; TODO
                      max-gap (min-key status-val stat stat-bound) new-src [s]))  
  (eq               [s other] (= (sws-vec s) (sws-vec other)))
  (>=               [s other bound] (not (neg? (compare (sws-vec s) (sws-vec other))))) ;; TODO: bound ???  
  (+                [s other new-src bound]
   (util/assert-is (sw-summary? other))
   (make-sw-summary*
    (clojure.core/+ min-rew (:min-rew other neg-inf))
    (clojure.core/min (clojure.core/+ f-val   (:f-val other neg-inf)) bound) ;; TODO
    (clojure.core/min (clojure.core/+ max-rew (:max-rew other)) bound)
    (clojure.core/max max-gap (:max-gap other Double/POSITIVE_INFINITY)) 
    (min-key status-val stat (status other))
    new-src [s other])))

(defn- make-sw-summary* [min-reward f-val max-reward max-gap status source children]
  (util/assert-is (<= min-reward f-val max-reward) "%s" [source children])
  (SimpleWeightedSummary. min-reward f-val max-reward max-gap status source children))

(defn make-sw-summary [min-reward max-reward status source children]
  (util/assert-is (contains? statuses-set status))
  (let [adj-min (clojure.core/max min-reward (* max-reward *sws-weight*))]
    (make-sw-summary* min-reward adj-min max-reward (- max-reward adj-min) status source children)))

(defn sw-summary? [s] (instance? SimpleWeightedSummary s))
(defmethod print-method SimpleWeightedSummary [s o]
  (print-method (str "SWSum:" [(:min-rew s) (:f-val s) (:max-rew s) (:max-gap s)] (status s)) o))














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
                     (make-interval-summary* min-rew (clojure.core/min max-rew bound)
                                             (min-key status-val stat stat-bound) new-src [s]))  
   (eq               [s other] (= (is-id-vec s) (is-id-vec other)))
   (>=               [s other bound] (not (neg? (compare (is-sort-vec s) (is-sort-vec other))))) ;; TODO: bound ???  
   (+                [s other new-src bound]
                     (make-interval-summary*
                      (clojure.core/+ min-rew (:min-rew other neg-inf))
                      (clojure.core/min (clojure.core/+ max-rew (max-reward other)) bound)
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


(defn- max-compare [cf arg1 & args]
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
