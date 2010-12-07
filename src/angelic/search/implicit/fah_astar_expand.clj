(ns angelic.search.implicit.fah-astar-expand
  (:require clojure.string
            [clojure.contrib.core :as ccc]
            [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs]
            [angelic.search.implicit.subproblem-expand :as subproblem])
  (:import  [java.util HashMap]))

;; A simple "tree" algorithm like AHA*, but with full subsumption propagation,
;; and no pseudo-rbfs problem.
;; Computation steps are expansions.

;;; TODOs:
;; Figure out subsumption edges
;;   - how does this interface with strategy?
;;   - we cannot be ezpected to verify all parents too ...
;;   - So, maybe forget about lazy for now ?
;; Propagate subsumption edges downwards (duh).

;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Solves the pseudo-RBFS problem.
;; Uses new traits approaches.
;; No pessimistic for now. 
;; This yields a sort of rightmost-first AHA*,
;; With upward propagation and caching

;; Right now, this works, except for lazy caching
;; (which must be fixed to not skip over OR-levels),
;; AND null output sets.  (In particular, for refine-input; immediate are fixed.) 

;; Note: used at compile-time, cannot be dynamically rebound without recompiling ...
#_ (def cache-trait summaries/uncached-summarizer-node)
 (def cache-trait summaries/eager-cached-summarizer-node)
#_ (def cache-trait summaries/lazy-cached-summarizer-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Atomic Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-simple-fs-seq-subproblem)

(defn refined-keys [sub-sp inp-set]
  (when-let [sub-child-keys (and sub-sp (summaries/expanded? sub-sp) (seq (subproblem/child-keys sub-sp)))]
    (util/for-map [k sub-child-keys]
      k (subproblem/refine-input (subproblem/get-child sub-sp k) inp-set))))


(defn make-simple-atomic-subproblem [sub-as inp-set function-set]
  (when-let [[out-set reward] (fs/apply-opt function-set inp-set)]
    (util/print-debug 3 "Making subproblem" (fs/fs-name function-set)
                      (fs/status function-set inp-set) reward)
    (traits/reify-traits
     [(subproblem/simple-subproblem
       [(fs/fs-name function-set) inp-set]
       inp-set out-set 
       (delay
         (or (refined-keys sub-as inp-set)            
           (let [fs-child-seqs (fs/child-seqs function-set inp-set)]
             (util/print-debug 2 "refs of " (fs/fs-name function-set) "are"
                               (map #(map fs/fs-name %) fs-child-seqs))
             (util/for-map [child fs-child-seqs]
               (map fs/fs-name child) (make-simple-fs-seq-subproblem inp-set child))))))      
      summaries/simple-node
      cache-trait
      (summaries/simple-or-summarizable
       (summaries/make-const-summarizable reward (fs/status function-set inp-set)))]
     subproblem/Refinable
     (refine-input- [s refined-input-set]
       (make-simple-atomic-subproblem s refined-input-set function-set)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Seq Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-simple-pair-subproblem)

(defn- make-aligned-simple-pair-subproblem [sub-ps sp1 sp2]
  (when sp1 (ccc/-?>> (subproblem/refine-input sp2 (subproblem/output-set sp1))
                      (make-simple-pair-subproblem sub-ps sp1))))

;; This is separate so we can handle child keys from other sps.
(defn simple-pair-child [sp1 sp2 child-key]
  (let [[which sub-key] child-key]
    (case which
      ::1 (ccc/-?> (subproblem/get-child sp1 sub-key) ((partial make-aligned-simple-pair-subproblem nil) sp2))
      ::2 (ccc/-?>> (subproblem/get-child sp2 sub-key) (make-simple-pair-subproblem nil sp1)))))


(defn force-child-keys [sp]
  (when-not (summaries/expanded? sp) (subproblem/expand! sp))
  (subproblem/child-keys sp))

(defn make-simple-pair-subproblem [sub-ps sp1 sp2]
  (let [seq-sum (traits/reify-traits [(summaries/fixed-node [sp1 sp2]) cache-trait
                                      summaries/simple-seq-summarizable])
        ret 
        (traits/reify-traits
         [(subproblem/simple-subproblem
           (gensym)
           (subproblem/input-set sp1) (subproblem/output-set sp2)
           (or (refined-keys sub-ps (subproblem/input-set sp1))
            (delay  (let [[l ks] (if (summary/live? (summaries/summary sp2))
                                   [::2 (force-child-keys sp2)]
                                   [::1 (force-child-keys sp1)])]
                      (util/for-map [k ks] [l k] (simple-pair-child sp1 sp2 [l k]))))))
          summaries/simple-node
          cache-trait
          (summaries/simple-or-summarizable seq-sum)]

         subproblem/Refinable
         (refine-input- [s refined-input-set]
           (make-aligned-simple-pair-subproblem s (subproblem/refine-input sp1 refined-input-set) sp2)))]
    (summaries/add-parent! seq-sum ret)
    ret))


(defn make-simple-fs-seq-subproblem [inp-set [first-fs & rest-fs]]
  (util/print-debug 2 "Making seq!:" (map fs/fs-name (cons first-fs rest-fs)))
  (when-let [first-sp (make-simple-atomic-subproblem nil inp-set first-fs)]
    (if (empty? rest-fs)
      first-sp
      (ccc/-?>> (make-simple-fs-seq-subproblem (subproblem/output-set first-sp) rest-fs)
                (make-simple-pair-subproblem nil first-sp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Driver ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn implicit-fah-a* [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       subproblem/solve))

;; (do (use 'edu.berkeley.ai.util '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.implicit-fah-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (implicit-fah-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))


;(let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 1 3))] (println #_ (run-counted #(his/interactive-hierarchical-search h)))  (println (run-counted #(implicit-fah-a* h))))



(comment
  (defmacro make-simple-atomic-subproblem [cache-trait inp-set function-set]
   `(let [inp-set# ~inp-set function-set# ~function-set
          [out-set# reward#] (fs/apply-opt function-set# inp-set#)]
      (util/print-debug 3 "Making subproblem" (fs/fs-name function-set#) (fs/status function-set# inp-set#) reward)
      (traits/reify-traits
       [(subproblem/simple-subproblem
         [(fs/fs-name function-set#) inp-set#]
         inp-set# out-set# 
         (delay (let [fs-child-seqs (fs/child-seqs function-set# inp-set#)]
                  (util/print-debug 2 "refs of " (fs/fs-name function-set#) "are" (map #(map fs/fs-name %) fs-child-seqs))
                  (into {} (map (juxt #(map fs/fs-name %) #(make-simple-fs-seq-subproblem inp-set# %)) fs-child-seqs))))
         #(make-simple-atomic-subproblem ~cache-trait % function-set#))
        summaries/simple-node
        ~cache-trait
        (summaries/simple-or-summarizable
         (summaries/make-const-summarizable reward# (fs/status function-set# inp-set#)))]))))