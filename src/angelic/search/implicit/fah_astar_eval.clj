(ns angelic.search.implicit.fah-astar-eval
  (:require clojure.string
            [clojure.contrib.core :as ccc]
            [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs]
            [angelic.search.implicit.subproblem-eval :as subproblem])
  (:import  [java.util HashMap]))

;; A simple "tree" algorithm like AHA*, but with full subsumption propagation,
;; and no pseudo-rbfs problem.
;; Computation steps are evaluations in this version.
;; Here, subproblems will never be nil -- but their output sets can be. 

;; TODO: figure out how lazy can interface with subsumption
;; TODO: pessimistic bounds 
;; This yields a sort of rightmost-first AHA*,
;; With upward propagation and caching

;; We also lazily evaluate refinements, for efficiency

;; TODO: this is really slow, mostly from summary stuff.
;; Looks like mostly useless propagation, with same summary but different ??
;; When is this really needed?  In lazy, it could all be avoided?
;; Also totally unnecessary -- updated solved summaries ?!

;; TODO: how exactly is this factored?
;; All plans are represented at top-level.
;; Argument was: without decomposition, this is just how it is.  More will be needed for that case.


;; Note: used at compile-time, cannot be dynamically rebound without recompiling ...
#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
 (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Atomic Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-simple-fs-seq-subproblem)

(defn- refined-keys [sub-sp inp-set]
  (when-let [sub-child-keys (and sub-sp (summaries/expanded? sub-sp) (seq (subproblem/child-keys sub-sp)))]
    (util/for-map [k sub-child-keys]
      k (subproblem/refine-input (subproblem/get-child sub-sp k) inp-set))))


(defn- make-simple-atomic-subproblem [sub-as inp-set function-set]
  (let [ls (traits/reify-traits [(summaries/fixed-node nil) cache-trait
                                 (summaries/leaf-summarizable (fs/fs-name function-set) 0 :live)])
        ret 
        (traits/reify-traits
         [(subproblem/simple-subproblem [(fs/fs-name function-set) inp-set] inp-set ls)
          summaries/simple-node
          cache-trait]

         subproblem/Refinable
         (evaluate- [s]
           (if-let [[out-set reward] (fs/apply-opt function-set inp-set)]
             (let [status (fs/status function-set inp-set)]
               (summaries/adjust-summary ls reward status)
               [out-set
                (when (= status :live)
                  (delay
                    (or (refined-keys sub-as inp-set)            
                        (let [fs-child-seqs (fs/child-seqs function-set inp-set)]
                          (util/for-map [child fs-child-seqs]
                                        (map fs/fs-name child) (make-simple-fs-seq-subproblem inp-set child))))))])
             (do (summaries/adjust-summary ls Double/NEGATIVE_INFINITY :blocked)
                 nil)))   
         (refine-input- [s refined-input-set]
                        (make-simple-atomic-subproblem s refined-input-set function-set)))]
    (summaries/add-parent! ls ret)
    ret))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Seq Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Idea here is to have PartialPairSubproblem.
;; Issues: want full propagation, but don't even know input set of second until first is eval'd.
;; That's not an issue -- partial pair always has first uneval'd.

(declare make-simple-pair-subproblem)


;; TODO: needed?
;; This is separate so we can handle child keys from other sps.
(defn- simple-pair-child [sp1 sp2 child-key]
  (let [[which sub-key] child-key]
    (case which
      ::1 (make-simple-pair-subproblem nil (subproblem/get-child sp1 sub-key) #(subproblem/refine-input sp2 %))
      ::2 (make-simple-pair-subproblem nil sp1 (constantly (subproblem/get-child sp2 sub-key))))))

;; TODO: lots of bubbling up first, when evaluate, then when create sp2 ...

;; I can be evaluated and expanded
;; sp2-fn takes input-set to sp2
(defn- make-simple-pair-subproblem [sub-ps sp1 sp2-fn]
;  (println "M" (util/truthify sub-ps) (first (subproblem/subproblem-name sp1)))
  (let [ss (traits/reify-traits [summaries/simple-node cache-trait
                                 (summaries/expanding-pair-summarizable sp1 nil)])
        sp2 (delay (assert (subproblem/evaluated? sp1))
                   (let [sp2 (sp2-fn (subproblem/output-set sp1))]
                     (summaries/set-right! ss sp2)
                     (summaries/connect! ss sp2 false)
                     (summaries/summary-changed! ss)
                     sp2))
        _   (when (subproblem/evaluated? sp1) (force sp2))
        ret 
        (traits/reify-traits
         [(subproblem/simple-subproblem (gensym) (subproblem/input-set sp1) ss)
          summaries/simple-node
          cache-trait]

         subproblem/Refinable
         (evaluate- [s]
           (if (not (subproblem/evaluated? sp1))
             (when (subproblem/evaluate! sp1) (force sp2) nil)                 
             (let [sp2 (force sp2)]
               (when-let [out (if (subproblem/evaluated? sp2) (subproblem/output-set sp2) (subproblem/evaluate! sp2))]
                [out
                 (delay
                  (or (refined-keys sub-ps (subproblem/input-set sp1))
                      (let [[l ks] (if (summary/live? (summaries/summary sp2))
                                     [::2 (subproblem/child-keys sp2)]
                                     [::1 (subproblem/child-keys sp1)])]
                        (util/for-map [k ks] [l k] (simple-pair-child sp1 sp2 [l k])))))]))))         
         (refine-input- [s refined-input-set]
                        (assert (subproblem/evaluated? sp1))
                        (make-simple-pair-subproblem s (subproblem/refine-input sp1 refined-input-set)
                                        #(subproblem/refine-input (force sp2) %))))]
    (summaries/connect! ss sp1 false)
    (summaries/add-parent! ss ret) ;; note uni-cxn
    ret))


(defn- make-simple-fs-seq-subproblem [inp-set [first-fs & rest-fs]]
  (let [first-sp (make-simple-atomic-subproblem nil inp-set first-fs)]
    (if (empty? rest-fs)
      first-sp
      (make-simple-pair-subproblem nil first-sp #(make-simple-fs-seq-subproblem % rest-fs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Driver ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn implicit-fah-a*-eval [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       subproblem/solve))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (time (run-counted #(implicit-fah-a*-eval (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))))

;(let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 1 3))] (println #_ (run-counted #(his/interactive-hierarchical-search h)))  (println (run-counted #(implicit-fah-a* h))))

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 3 1 0) true)]  (println (run-counted #(second (implicit-fah-a*-eval h))) @summaries/*summary-count*)))))

;;(require '[angelic.search summary summaries] '[angelic.search.implicit subproblem-eval subproblem-expand fah-astar-eval fah-astar-expand] :reload)