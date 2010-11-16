(ns angelic.search.implicit.implicit-fah-astar
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs]
            [angelic.search.implicit.subproblem :as subproblem])
  (:import  [java.util HashMap]))


;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Solves the pseudo-RBFS problem.
;; Uses new traits approaches.
;; No pessimistic for now. 

;; This is where key difference comes in from earlier --
;; sum is live in earnest itself ?
;; IE if sum is ever live, it is live directly (no descendants) ? IE we update the whole vertical chain?  bad news ... ?

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simple FS Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Very simple, no caching or reuse or anything.
;; This yields a sort of rightmost-first AHA*,
;; With upward propagation and caching ?

(declare make-simple-fs-seq-subproblem)

(defn make-simple-atomic-subproblem [inp-set function-set]
  (let [[out-set reward] (fs/apply-opt function-set inp-set)]
    (util/print-debug 3 "Making subproblem" (fs/fs-name function-set) (fs/status function-set inp-set) reward)
    (traits/reify-traits
     [(subproblem/simple-subproblem
       [(fs/fs-name function-set) inp-set]
       inp-set out-set 
       (delay (let [fs-child-seqs (fs/child-seqs function-set inp-set)]
                (util/print-debug 2 "refs of " (fs/fs-name function-set) "are" (map #(map fs/fs-name %) fs-child-seqs))
                (into {} (map (juxt #(map fs/fs-name %) #(make-simple-fs-seq-subproblem inp-set %)) fs-child-seqs))))
       #(make-simple-atomic-subproblem % function-set))
      summaries/simple-node
      summaries/eager-cached-summarizer-node
      (summaries/simple-or-summarizable
       (summaries/make-const-summarizable reward (fs/status function-set inp-set)))])))



(declare make-simple-pair-subproblem)

(defn- make-aligned-simple-pair-subproblem [sp1 sp2]
  (make-simple-pair-subproblem sp1 (subproblem/refine-input sp2 (subproblem/output-set sp1))))


(defn simple-pair-child [sp1 sp2 child-key]
  (let [[which sub-key] child-key]
    (case which
      ::1 (make-aligned-simple-pair-subproblem (subproblem/get-child sp1 sub-key) sp2)
      ::2 (make-simple-pair-subproblem sp1 (subproblem/get-child sp2 sub-key)))))


(defn force-child-keys [sp]
  (when-not (summaries/expanded? sp) (subproblem/expand! sp))
  (subproblem/child-keys sp))

(defn make-simple-pair-subproblem [sp1 sp2]
  (let [seq-sum (traits/reify-traits [(summaries/fixed-node [sp1 sp2]) summaries/eager-cached-summarizer-node summaries/simple-seq-summarizable])
        ret 
        (traits/reify-traits
         [(subproblem/simple-subproblem
           (gensym)
           (subproblem/input-set sp1) (subproblem/output-set sp2)
           (delay (let [[label ks] (if (summary/live? (summaries/summary sp2)) [::2 (force-child-keys sp2)] [::1 (force-child-keys sp1)])]
                    (into {} (for [k ks] [[label k] (simple-pair-child sp1 sp2 [label k])]))))
           #(make-aligned-simple-pair-subproblem (subproblem/refine-input sp1 %) sp2))
          summaries/simple-node
          summaries/eager-cached-summarizer-node
          (summaries/simple-or-summarizable seq-sum)])]
    (summaries/add-parent! seq-sum ret)
    ret))


(defn make-simple-fs-seq-subproblem [inp-set [first-fs & rest-fs]]
  (util/print-debug 2 "Making seq!:" (map fs/fs-name (cons first-fs rest-fs)))
  (let [first-sp (make-simple-atomic-subproblem inp-set first-fs)]
    (if (empty? rest-fs)
      first-sp
      (->> (make-simple-fs-seq-subproblem (subproblem/output-set first-sp) rest-fs)
           (make-simple-pair-subproblem first-sp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;; TopDown FS Subproblem ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Add caching, exploitation of subsumption, but no graphiness 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At least two ways we can do it -- keeping set of leaves, or following sum structure.
;; Do the latter for now.
;; Problem: haven't exposed enough. In particular, no way to verify through seqs.

(def make-root-node make-simple-atomic-subproblem)

(defn implicit-fah-a* [henv]
  (->> (function-sets/make-init-pair henv)
       (apply make-root-node)
       subproblem/solve))


;; (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.implicit-fah-astar)
;; (implicit-random-fah-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))






;; TODO: getting child from super ...


;; TODO: simple generic SimpleSubproblem record ? 

;; TODO: stop early on empty sets or bad rewards, etc.




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Wrapped Seq ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment 
 (defrecord WrappedSubproblem [input-set wrapped-sp remaining-keys output-set]
   Subproblem
   (current-summary [s] ...)
   (child-keys      [s] [(first remaining-keys)])
   (get-child       [s child-key]
                    (assert (= child-key (first remaining-keys)))
                    (let [inner-child (get-child wrapped-sp child-key)
                          more-keys   (next remaining-keys)]
                      (if more-keys
                        (make-wrapped-subproblem inner-child more-keys output-set)
                        (do (assert (state-set/subset? (:output-set inner-child) output-set))
                            inner-child))))
   (refine-input    [s refined-input-set]
                    ...?))

 (defn make-wrapped-subproblem [wrapped-sp remaining-keys output-set]
   (WrappedSubproblem. (input-set wrapped-sp) wrapped-sp remaining-keys output-set)))

