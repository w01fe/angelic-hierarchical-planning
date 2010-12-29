(ns angelic.search.implicit.fah-astar-eval2
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList]))

;; A version of eval subproblems where we explicitly represent the relationships
;; between subproblems, and allow "listeners" that wait for a subproblem to be
;; evaluated.

;; This version has a few problems, not least multiple generation,
;; and some dangling inconsistency.

;; Breaks down into "subproblems" with well-defined action seqs, inputs, outputs,
;; and "stubs" where output is not known yet.
;; Summary of either represents child subproblems not yet produced.
;; These are produced into "tree summary", which has semantic view.

(set! *warn-on-reflection* true)

;; TODO: note lazy is so lazy about subsumption , ...

#_ (def  ^{:private true} cache-trait summaries/uncached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/eager-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/less-eager-cached-summarizer-node)
 (def ^{:private true} cache-trait summaries/lazy-cached-summarizer-node)
#_ (def ^{:private true} cache-trait summaries/pseudo-cached-summarizer-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Watched
  (add-watcher! [s w] "Add a watcher to be notified of all outputs to this.
                         A watcher is just a fn of [watched-sp/stub new-subproblem].")
  (add-output!  [sw o]    "O is a subproblem"))

;; TODO: doall is bug ? 
(traits/deftrait simple-watched
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)]
  []
  Watched
  (add-watcher! [sw w] #_(println :AW sw w)
    (.add watchers w)
    (doseq [o (doall (seq outputs))] (w sw o))#_ (println :WF sw))
  (add-output! [sw o] #_ (println :AO sw o)
    (.add outputs o)
    (doseq [w (doall (seq watchers))] (w sw o)) #_(println :OF sw)))


;; Note: this entails zero minimum cost (i.e., nonnegative costs).
(defn subsuming-bound [s]
  (->> (summaries/node-subsuming-children s)
       (map (comp summary/max-reward summaries/summary))
       (apply min 0)))

(defn or-summary [s b]
  (summary/or-combine (map summaries/summary (summaries/node-ordinary-children s)) s b))


(traits/deftrait or-summarizable [] [] []
  summaries/Summarizable (summarize [s] (or-summary s (subsuming-bound s))))

(traits/deftrait simple-cached-node [] [] [summaries/simple-node cache-trait])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Protocols     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Evaluable
  (evaluate!      [s]))

(defn can-evaluate? [s]
  (instance? angelic.search.implicit.fah_astar_eval2.Evaluable s))

;; Stub implements node, watched, possibly Evaluable, cached, Summarizable
;;  -- Has at most a single output.

(defprotocol Stub
  (stub-name   [s])
  (input-set   [s]))

(traits/deftrait simple-stub [name inp] [] [] Stub (input-set [s] inp) (stub-name [s] name))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (tree-summarizer   [s] "Summarizer that includes children.")
  (terminal?         [s] "Subproblem will not return further outputs.")
  (refine-input      [s refined-input-set] "Return a child stub.")

  (top-down-bound    [s])
  (add-top-down-bound! [s b]))

(defn subproblem-name [s] (stub-name (stub s)))

(defn add-child-sp! [sp c]
  (connect-child-sp! (tree-summarizer sp) c))

(defmethod print-method angelic.search.implicit.fah_astar_eval2.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (subproblem-name sp)) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tree Summarizer  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expects to be a parent of inside, but not have inside as a child.
;; All children are tree summarizers.
;; Non-subsuming children must be added by calling connect-child-sp!
(defprotocol TreeSummarizer
  (connect-child-sp! [ts child-sp])
  (get-inner-sp      [ts] "Get subproblem for this ts"))


(defn make-tree-summarizer [inner-sp assert-monotonic?]
 (let [last-sum (atom nil)]
  (traits/reify-traits [simple-cached-node simple-watched]
   TreeSummarizer
   (get-inner-sp [ts] inner-sp)
   (connect-child-sp! [ts child-sp]
     (summaries/connect! ts (tree-summarizer child-sp) false)
     (add-top-down-bound! child-sp (top-down-bound inner-sp))
     (add-output! ts child-sp)
     (let [my-sum (summaries/summary ts)
           child-sum (summaries/summary (tree-summarizer child-sp))]
       (when assert-monotonic?
         (util/assert-is (>= (summary/max-reward my-sum) (summary/max-reward child-sum)) "%s" [:AC (def *sum* ts) (def *child-sp* child-sp) inner-sp (subsuming-bound ts)]))
       (when-not (summary/>= my-sum child-sum) ;         (println "New child inc" my-sum child-sum ts child-sp)
         (summaries/summary-changed! ts))))
    
   summaries/Summarizable
   (summarize [s]
     (swap! summaries/*summary-count* inc)
     (let [sum (summary/or-combine
                 (cons (summaries/summary inner-sp)
                       (map summaries/summary (summaries/node-ordinary-children s)))
                 s (subsuming-bound s))]
       (when (and assert-monotonic? @last-sum)
       (util/assert-is (>= (summary/max-reward @last-sum) (summary/max-reward sum)) "%s" [:s (def *sum* s) inner-sp]))
       (reset! last-sum sum))))))




(defn ts-str [sp])
(defmethod print-method angelic.search.implicit.fah_astar_eval2.TreeSummarizer [ts o]
  (let [stub (stub (get-inner-sp ts))]
    (print-method (format "#<TS$%8h %s>" (System/identityHashCode stub) (stub-name stub)) o)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblem Impl  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-simple-subproblem
  [stub subsuming-sp out-set terminal? summary-fn ri-fn init-bound]
  (let [ts-atom (atom nil)
        tdb-atom (atom init-bound) ;; TODO: factor out into trait?
        ret (traits/reify-traits [simple-cached-node]
             summaries/Summarizable (summarize       [s] (summary-fn s @tdb-atom))
             Subproblem             (stub            [s] stub)
                                    (output-set      [s] out-set)
                                    (tree-summarizer [s] @ts-atom)
                                    (terminal?       [s] terminal?)
                                    (refine-input    [s ni]
                                      (if (= ni (input-set stub)) stub (ri-fn s ni)))
                                    (top-down-bound [s] @tdb-atom)
                                    (add-top-down-bound! [s b]
                                      (when (< b @tdb-atom)
                                        (reset! tdb-atom b)
                                        (summaries/summary-changed! s))))]
    (reset! ts-atom (make-tree-summarizer ret true #_(= :Atomic (first name))))
    (summaries/add-parent! ret @ts-atom false)
    (when subsuming-sp (summaries/connect! (tree-summarizer ret) (tree-summarizer subsuming-sp) true))
    ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;     Subproblem Types and Stubs     ;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare make-fs-seq-stub make-atomic-stub)

(defn connect-and-watch! [p c f]
  (summaries/connect! p c false)
  (add-watcher! c (fn [_ o] (f o))))

;; TODO: pass reward through so it propagates through outputs.
;; How to do this elegantly ? 
(defn- make-atomic-subproblem [stub function-set subsuming-sp out-set reward status]
  (let [inp-set  (input-set stub)
        ri-fn    (fn [s ri] (make-atomic-stub s ri function-set))]
    (cond (not (= status :live))
          (make-simple-subproblem
           stub subsuming-sp out-set true
           (fn [s b] (summary/make-simple-summary (min b reward) status s)) ri-fn reward)
          
          (and subsuming-sp (not (terminal? subsuming-sp)))
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false or-summary ri-fn reward)]
            (summaries/connect! ret subsuming-sp false)
            (add-watcher! (tree-summarizer subsuming-sp)
              (fn [_ sub-out] (connect-and-watch! ret (refine-input sub-out inp-set)
                                                  #(add-child-sp! ret %))))
            ret)
          
          :else 
          (let [ret (make-simple-subproblem stub subsuming-sp out-set false or-summary ri-fn reward)]
            (doseq [child (map #(make-fs-seq-stub inp-set %) (fs/child-seqs function-set inp-set))]
              (connect-and-watch! ret child #(add-child-sp! ret %)))            
            ret))))




(defn connect-subsuming! [child subsuming-sp]
  (when subsuming-sp (summaries/connect! child (tree-summarizer subsuming-sp) true)))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [subsuming-sp inp-set function-set]
  (let [state (atom :ready) ;; set to [out-set reward] after first eval, then :go after second.
        ret
        (traits/reify-traits
         [(simple-stub [:Atomic (fs/fs-name function-set) #_ inp-set] inp-set)
          simple-watched simple-cached-node]
         summaries/Summarizable
         (summarize [s]
           (cond (= :ready @state) (summary/make-live-simple-summary (subsuming-bound s) s)
                 (= :go    @state) summary/+worst-simple-summary+
                 :else             (summary/make-live-simple-summary (second @state) s)))   
         Evaluable
         (evaluate! [s]
           (assert (not (= :go @state)))
           (let [ready?                  (= :ready @state)]
             (if-let [[out-set reward :as op] (if ready? (fs/apply-opt function-set inp-set) @state)]
               (let [status (if ready? (fs/status function-set inp-set)   :live)]
                 (if (or (not ready?) (not (= status :live)))
                   (do (add-output! s (make-atomic-subproblem s function-set subsuming-sp
                                                              out-set reward status))
                       (reset! state :go))
                   (reset! state op)))
               (reset! state :go)) ;; Kill it
             (summaries/summary-changed! s))))]
    (connect-subsuming! ret subsuming-sp)
    ret))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)

;; TODO: fix up subsuming, parent, etc. 
(defn- make-pair-subproblem [subsuming-sp pair-stub #_ parent-sp left-sp right-sp]
  (let [expand-right? (terminal? left-sp) ;; TODO: not right..., plus change.
        kids (if expand-right? [right-sp (tree-summarizer left-sp)]
                 [left-sp (tree-summarizer right-sp)])
        ret (make-simple-subproblem
             pair-stub subsuming-sp (output-set right-sp) false             
             (fn [s b] (summary/max
                        (or-summary s b)
                        (summary/+ (summaries/summary (first kids))
                                   (summaries/summary (second kids)) s b)))
             (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                                         (subproblem-name right-sp) #(refine-input right-sp %)))
             0)]
    (doseq [k kids] (summaries/add-parent! k ret false))
    (add-watcher! (tree-summarizer (first kids))
      (fn [_ o] (connect-and-watch! ret
                  (if expand-right? 
                    (make-pair-stub2 nil left-sp (stub o))
                    (make-pair-stub2 nil o (refine-input right-sp (output-set o))))
                  #(add-child-sp! ret %))))
    ret))

;; TODO: remove children as they are no longer needed ?
(defn- make-pair-stub2 [subsuming-sp left-sp right-stub]
  (let [ret (traits/reify-traits
             [simple-cached-node simple-watched
              (simple-stub [:Pair (subproblem-name left-sp) (stub-name right-stub)]
                            (input-set (stub left-sp)))]
              summaries/Summarizable
              (summarize [s]
               (summary/+ (summaries/summary (tree-summarizer left-sp))
                          (summaries/summary right-stub)
                          s (subsuming-bound s))))]
    (connect-subsuming! ret subsuming-sp)
    (summaries/connect! ret (tree-summarizer left-sp) false)
    (connect-and-watch! ret right-stub
      #(add-output! ret (make-pair-subproblem subsuming-sp ret left-sp %)))
    ret))

;; TODO: we need to liven left-stub ??
(defn- make-pair-stub1 [subsuming-sp left-stub right-name right-stub-fn]
  (let [ret (traits/reify-traits [simple-cached-node simple-watched or-summarizable
                                  (simple-stub [:Pair1 (stub-name left-stub) right-name]
                                               (input-set left-stub))])]
    (connect-subsuming! ret subsuming-sp)
    (connect-and-watch! ret left-stub
      (fn [lo] (connect-and-watch! ret
                 (make-pair-stub2 subsuming-sp lo (right-stub-fn (output-set lo)))
                 #(add-output! ret %))))    
    ret))


(defn- make-fs-seq-stub
  ([inp-set fs] (make-fs-seq-stub inp-set fs (map fs/fs-name fs)))
  ([inp-set [first-fs & rest-fs] fs-names]
     (let [left-stub (make-atomic-stub nil inp-set first-fs)]
       (if (empty? rest-fs)
         left-stub
         (make-pair-stub1 nil left-stub (rest fs-names)
                          #(make-fs-seq-stub % rest-fs (rest fs-names)))))))


  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- choose-leaf [verified-summary]
;  (println "VS"  verified-summary)  (def *sum* verified-summary) (Thread/sleep 10)
  (->> (summary/extract-leaf-seq verified-summary (comp empty? summary/children))
;       util/prln
;       (#(do (def *bads* %) %))
       (map summary/source)
;       util/prln
;       (#(do (def *bad* %) %))
       (filter can-evaluate?)
       last #_ rand-nth))

(defn- solve [root-subproblem]
  (def *root* root-subproblem)
  (summary/solve
   #(summaries/verified-summary (tree-summarizer root-subproblem) summary/+worst-simple-summary+)
   (comp evaluate! choose-leaf)
   #(let [n (second (subproblem-name %))] (when-not (= (first n) :noop) n))))

(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil inp-set fs)
        ret       (atom nil)]
    (add-watcher! root-stub (fn [_ root] (reset! ret root)))
    (evaluate! root-stub)
    (evaluate! root-stub)
;    (println root-stub (summaries/summary root-stub) ret)
    (assert @ret)
    @ret))


(defn implicit-fah-a*-eval2 [henv]
  (->> (fs/make-init-pair henv)
       (apply get-root-subproblem)
       solve))

; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.fah-astar-eval2 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-fah-a*-eval2 h))) @summaries/*summary-count*)) )))









;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Graveyard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(comment
  (defn pseudo-solve [root-sp]
   (summaries/pseudo-solve root-sp summary/+worst-simple-summary+ (complement summaries/expanded?)
                           #(if (evaluated? %) (do (assert (not (summaries/expanded? %))) (child-keys %)) (evaluate! %))))

  
  (defn implicit-fah-a*-eval-pseudo [henv]
  (->> (fs/make-init-pair henv)
       (apply make-simple-atomic-subproblem nil)
       subproblem/pseudo-solve)))

