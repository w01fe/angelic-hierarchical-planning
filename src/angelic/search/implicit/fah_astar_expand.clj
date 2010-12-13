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
;; and no pseudo-rbfs problem.  Always expands rightmost thing?
;; Computation steps are expansions.

;; TODO: figure out how lazy can interface with subsumption
;; TODO: pessimistic bounds 
;; This yields a sort of rightmost-first AHA*,
;; With upward propagation and caching


;; Note: used at compile-time, cannot be dynamically rebound without recompiling ...
#_ (def ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)

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
       inp-set
       [out-set (traits/reify-traits [(summaries/leaf-summarizable (fs/fs-name function-set) reward (fs/status function-set inp-set))
                                      cache-trait (summaries/fixed-node nil)])] 
       (delay
         (or (refined-keys sub-as inp-set)            
           (let [fs-child-seqs (fs/child-seqs function-set inp-set)]
             (util/print-debug 2 "refs of " (fs/fs-name function-set) "are"
                               (map #(map fs/fs-name %) fs-child-seqs))
             (util/for-map [child fs-child-seqs]
               (map fs/fs-name child) (make-simple-fs-seq-subproblem inp-set child))))))      
      summaries/simple-node
      cache-trait]
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
                                      (summaries/expanding-pair-summarizable sp1 sp2)])
        ret 
        (traits/reify-traits
         [(subproblem/simple-subproblem
           (gensym)
           (subproblem/input-set sp1)
           [(subproblem/output-set sp2) seq-sum]
           (or (refined-keys sub-ps (subproblem/input-set sp1))
            (delay  (let [[l ks] (if (summary/live? (summaries/summary sp2))
                                   [::2 (force-child-keys sp2)]
                                   [::1 (force-child-keys sp1)])]
                      (util/for-map [k ks] [l k] (simple-pair-child sp1 sp2 [l k]))))))
          summaries/simple-node
          cache-trait]

         subproblem/Refinable
         (refine-input- [s refined-input-set]
           (make-aligned-simple-pair-subproblem s (subproblem/refine-input sp1 refined-input-set) sp2)))]
    (summaries/add-parent! seq-sum ret false)
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

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (implicit-fah-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))

;(let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 1 3))] (println  (run-counted #(his/interactive-hierarchical-search h)))  (println (run-counted #(implicit-fah-a* h))))

;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 1 3))]  (println (run-counted #(second (implicit-fah-a* h))) @summaries/*summary-count*)))))