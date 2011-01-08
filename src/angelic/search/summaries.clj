(ns angelic.search.summaries
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.search.summary :as summary])
  (:import [java.util ArrayList]))

;; This file defines a dataflow-style API for computing and caching
;; summaries of potentially mutable objects.

;; The basic idea here is to separate these statistics and their
;; propagation and caching from the generation of the search space


(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Node
  (node-ordinary-children   [n])
  (node-subsuming-children  [n])
  (node-ordinary-parents   [n])
  (node-subsumed-parents   [n])    
  (add-parent!     [n parent-node sub?])
  (add-child!      [n child-node sub?])
  (remove-parent!     [n parent-node ])
  (remove-child!      [n child-node ])  )

(defprotocol SummaryCache
  (summary [n] "Possibly cached version of summarize")
  (summary-changed! [n] "Update summary and notify parents as needed")
  (summary-changed-local! [n] "Just update local summary, no parent notification (pot'l unsafe)")
  (verified-summary [n min-summary] "Return a current exact best summary >= min-summary, or nil"))



(def *summary-count* (atom 0))

(defprotocol Summarizable
  (summarize [s] "Compute a summary based on the 'summary' of children, if applicable."))

(def *use-subsumption* true)
(def *assert-consistency* false #_true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Traits ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-node [] [^java.util.ArrayList children (java.util.ArrayList.)
                                 ^java.util.ArrayList parents  (java.util.ArrayList.)] []
  Node
  (node-ordinary-children [n] (map second (remove first (seq children))))
  (node-subsuming-children [n] (map second (filter first (seq children))))
  (node-ordinary-parents [n] (map second (remove first (seq parents))))
  (node-subsumed-parents [n] (map second (filter first (seq parents))))    
  (add-child!    [n child subsuming?] (assert (not (identical? child n)))
    (.add children [subsuming? child]))
  (add-parent!   [n parent subsuming?] (assert (not (identical? parent n)))
    (.add parents [subsuming? parent]))
  (remove-child! [n child]
    (let [i (util/position-if #(identical? (second %) child) children)]
      (.remove children (int i))))  
  (remove-parent! [n parent]
    (let [i (util/position-if #(identical? (second %) parent) parents)]
      (.remove parents (int i))))  
  )

(traits/deftrait fixed-node [children] [^java.util.ArrayList sub-children (java.util.ArrayList.)
                                        ^java.util.ArrayList parents (java.util.ArrayList.)] []
   Node
   (node-ordinary-children [n] children)
   (node-subsuming-children [n] (seq sub-children))   
   (node-ordinary-parents [n] (map second (remove first (seq parents))))
   (node-subsumed-parents [n] (map second (filter first (seq parents))))    
   (add-child!    [n child sub?]
      (assert sub?)
      (.add sub-children child))
   (add-parent!   [n parent subsuming?] (.add parents [subsuming? parent]))
  (remove-child! [n child]
    (let [i (util/position-if #(identical? % child) sub-children)]
      (.remove sub-children (int i))))  
  (remove-parent! [n parent]
    (let [i (util/position-if #(identical? (second %) parent) parents)]
      (.remove parents (int i))))
   )



(defn connect! [parent child subsuming?]
  (when (or (not subsuming?) *use-subsumption*)
    (add-parent! child parent subsuming?)
    (add-child! parent child subsuming?)))

(defn disconnect! [parent child ]
  (remove-parent! child parent )
  (remove-child! parent child ))

(defn node-parents [n] (concat (node-ordinary-parents n) (node-subsumed-parents n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SummaryCache ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Problem with making these true traits are that:
;; (1) no enforcement that all nodes use the same trait
;; (2) no way to select at runtime.

;; In retrospect, probably would be better to bite the bullet and say
;; "a node has a cache", but for now we just hack it with binding?

;; Can be :uncached, :eager, :lazy, :eager-nosub, :eager-content, ...?
;; TODO: offer a variant of :eager-content that just extracts a leaf.
(def *cache-method* nil)


(traits/deftrait summary-cache [] [cache (atom nil)] []
  SummaryCache
  (summary [n]
    (if (= :uncached *cache-method*)
      (summarize n)
      (or @cache (do (assert (#{:eager :eager-nosub :eager-nokids :lazy } *cache-method*))
                     (reset! cache (summarize n))))))
  (summary-changed! [n]
    (when-let [old @cache]
      (let [new (summarize n)]
        (when *assert-consistency*
          (util/assert-is (<= (summary/max-reward new) (summary/max-reward old))))
        (when-not (summary/solved? old)
          (if (#{:eager :eager-nosub} *cache-method*)
            (when-not (= old new)
              (reset! cache new)
              (doseq [p (doall ((case *cache-method* :eager-nosub node-ordinary-parents :eager node-parents) n))]
                (summary-changed! p)))
            (do (reset! cache new)
                (when-not ((case *cache-method* :lazy summary/>= :eager-nokids summary/eq) old new)
                  (doseq [p (doall (node-parents n))]
                    (summary-changed! p)))))))))
  (summary-changed-local! [n]
    (if  (#{:eager :eager-nosub} *cache-method*)
      ;      when-let [old @cache] ;; TODO: why does this hurt?
       (let [new (summarize n)]
        (when-not (= @cache new)
          (reset! cache new)))
      (reset! cache nil)))
  (verified-summary [n min-summary]
   (case *cache-method*
     :lazy
     (let [os @cache
           cs (reset! cache (summarize n))]
;       (swap! *summary-count* dec)
       (when os (util/assert-is (<= (summary/max-reward cs) (summary/max-reward os))))
       (when (summary/>= cs min-summary)
         (let [verified-children (map #(verified-summary (summary/source %) %) (util/unchunk (summary/children cs)))]
           (if (every? identity verified-children)
             (reset! cache (summary/re-child cs verified-children))
             (recur min-summary)))))

     :eager-nokids
      (let [cs (summary n)]
        (when (summary/>= cs min-summary)
          (let [verified-children (map #(verified-summary (summary/source %) %) (summary/children cs))]
            (assert (every? identity verified-children))
            (reset! cache (summary/re-child cs verified-children)))))
      
      
      (let [cs (summary n)] ;else
        (when (summary/>= cs min-summary)
          cs)))))

(comment ;;mods for better consistency -- didn't really help
            (when-not equal? (reset! cache new))
  
  (when-not (= :uncached *cache-method*) ;; for local
      (let [new (summarize n)]
        (when-not (= @cache new)
          (reset! cache new))))  
 )



(comment 

 ;; No notification, just pseudo-rbfs solution (which may refine suboptimal things)
 ;; Can't quite replicate earlier, since we don't have control over AND expansion order...
 ;; Can't use verified-summary since we need eval going up too.
 ;; TODO: improve min-summary handling ?
 ;; TODO: doesn't work right now, since deeper stuff doesn't get evaluated.
 ;; Need to think harder about separation of concerns, how to cross-cut ?
 (defprotocol PseudoSolver
   (pseudo-solve [n min-summary stop? evaluate!]))

(traits/deftrait pseudo-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n] (reset! summary-cache (summarize n)))
  (verified-summary [n min-summary] (throw (UnsupportedOperationException.)))
  PseudoSolver
  (pseudo-solve [n min-summary stop? evaluate!]
    (let [os @summary-cache
          cs (reset! summary-cache (summarize n))]
      (when os (assert (<= (summary/max-reward cs) (summary/max-reward os))))
      ;      (println min-summary cs (angelic.search.implicit.subproblem-eval/subproblem-name (summary/source cs)) (angelic.search.implicit.subproblem-eval/evaluated? (summary/source cs)) (expanded? (summary/source cs)) #_  (summary/source cs)) (Thread/sleep 10)
      (cond (not (summary/>= cs min-summary)) nil
            (summary/solved? cs) cs
            (stop? n) (do (println "\nEVAL!") (evaluate! n) (recur min-summary stop? evaluate!))
            :else (let [child (util/safe-singleton (summary/children cs))]
                    (pseudo-solve (summary/source child) child stop? evaluate!)
                    (recur min-summary stop? evaluate!)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summarizable ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; Note: this entails zero minimum cost (i.e., nonnegative costs).
(defn subsuming-bound [s]
  (->> (node-subsuming-children s)
       (map (comp summary/max-reward summary))
       (apply min 0)))

(defn or-summary [s b]
  (swap! *summary-count* inc)
  (summary/or-combine (map summary (node-ordinary-children s))
                      s (min (subsuming-bound s) b)))


(traits/deftrait or-summarizable [] [] []
  Summarizable (summarize [s] (or-summary s 0)))

(traits/deftrait simple-cached-node [] [] [simple-node summary-cache])

(defn sum-summary [s b]
  (swap! *summary-count* inc)
  (let [children (node-ordinary-children s)]
    (assert (= (count children) 2))
    (summary/+ (summary (first children)) (summary (second children))
               s (min b (subsuming-bound s)))))

(traits/deftrait sum-summarizable [] [] []
  Summarizable (summarize [s] (sum-summary s 0)))

(defn make-sum-summarizer [kids]
  (let [ret (traits/reify-traits [sum-summarizable simple-cached-node])]
    (doseq [kid kids] (connect! ret kid false))
    ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searching ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *root* nil)
(defn solve [root-summarizable operate-on-best-leaf-seq! action-extractor]
  (def *root* root-summarizable)
  (summary/solve
   #(verified-summary root-summarizable summary/+worst-simple-summary+)
   #(operate-on-best-leaf-seq! (summary/extract-leaf-source-seq %))
   action-extractor))
















;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Junk for olg algs that should eventually go away ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; New-bound is a summarizable.
(defprotocol Expandable
  (expanded?   [s])
  (expand!     [s children]))

(defprotocol LeafSummarizable
  (label [s])
  (adjust-summary [s new-reward new-status]))

(traits/deftrait leaf-summarizable [label reward status] [pair-atom (atom [reward status])] []
  Summarizable
  (summarize [s]
   (swap! *summary-count* inc)
   (let [[rew st] @pair-atom] (summary/make-simple-summary rew st s)))
  LeafSummarizable
  (label [s] label)
  (adjust-summary [s new-rew new-st] (reset! pair-atom [new-rew new-st]) (summary-changed! s)))

;; Note: no need for bound-subsuming here. 

(comment
 (defn make-leaf-summarizable [reward status]
   (traits/reify-traits [simple-node uncached-summarizer-node (leaf-summarizable reward status)]))
)



;; Initially shoud be a parent of init, without having child.

(traits/deftrait simple-or-summarizable [init] [expanded?-atom (atom false)] []
   Expandable
   (expanded? [s] @expanded?-atom)
   (expand!   [s child-summarizers]
     (assert (not (expanded? s)))
     (reset! expanded?-atom true)
     (doseq [child child-summarizers] (connect! s child false))
     (summary-changed! s))
   Summarizable
   (summarize [s]
     (swap! *summary-count* inc)
     (let [init-summary (summary init)
           bound        (summary/max-reward (apply summary/min (map summary (node-subsuming-children s))))]
       (if (not (and (summary/live? init-summary) (expanded? s)))
         (summary/or-combine [init-summary] s bound)
         (summary/or-combine (map summary  (node-ordinary-children s)) s (min bound (summary/max-reward init-summary)))))))

(defn extract-unexpanded-leaf [summary]
  (summary/extract-single-leaf summary #(not (expanded? (summary/source %)))))

(defn extract-verified-unexpanded-leaf [summarizable]
  (let [s (verified-summary summarizable summary/+worst-simple-summary+)]
    (if (summary/solved? s) s (extract-unexpanded-leaf s))))


;; These ones need children set from outside...

(defprotocol ExpandingPairSummarizable (set-right! [s right]))

(traits/deftrait expanding-pair-summarizable [left right?] [right-atom (atom right?)] []
  Summarizable
  (summarize [s]
    (swap! *summary-count* inc)         
    (assert (empty? (node-subsuming-children s)))
    (if-let [right @right-atom]
      (summary/+ (summary left) (summary right) s)
      (summary/liven (summary left) s)))
  
  ExpandingPairSummarizable
  (set-right! [s right] (reset! right-atom right)))

(traits/deftrait simple-pair-summarizable [left right] [] [(expanding-pair-summarizable left right)])




(defn notify-parents [n]
  (doseq [p (doall (node-parents n))]
    (summary-changed! p)))

(defn notify-ordinary-parents [n]
  (doseq [p (doall (node-ordinary-parents n))]
    (summary-changed! p)))

(defn default-verified-summary [n min-summary]
  (let [cs (summary n)]
    (when (summary/>= cs min-summary)
      cs)))

(defn update-cache! [n cache-atom]
  (when-let [old @cache-atom]
    (let [new (summarize n)]
      (when-not (summary/solved? old) 
        (when *assert-consistency*
          (util/assert-is (<= (summary/max-reward new) (summary/max-reward old))
                          "%s" [(def *bad* n)]))     
        (reset! cache-atom new)
        (not (= old new))))))


(traits/deftrait uncached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (summarize n))
  (summary-changed! [n] nil)
  (summary-changed-local! [n] nil)
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))


(traits/deftrait eager-cached-summarizer-node [] [] []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (when (update-cache! n summary-cache)
      (notify-parents n)))
  (summary-changed-local! [n] (reset! summary-cache nil))
  (verified-summary [n min-summary]
    (default-verified-summary n min-summary)))

;; Eager except about subsumption, which is just accidental
(traits/deftrait less-eager-cached-summarizer-node [] [summary-cache (atom nil)] []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]    
    (when (update-cache! n summary-cache)
      (notify-ordinary-parents n)))
  (summary-changed-local! [n] (reset! summary-cache nil))
  (verified-summary [n min-summary] (default-verified-summary n min-summary)))



;; Only notifies when summary increases ...
;; TODO: figure out best v-s method. -- avoid thrashing ? 
;; NOTE: efficiency depends on consistency of child ordering ...
(traits/deftrait lazy-cached-summarizer-node [] [summary-cache (atom nil)]  []
  SummaryCache
  (summary [n] (or @summary-cache (reset! summary-cache (summarize n))))
  (summary-changed! [n]
    (let [os @summary-cache
          ns (reset! summary-cache (summarize n))]
      (when os
        (when *assert-consistency* (util/assert-is (<= (summary/max-reward ns) (summary/max-reward os))))      
        (when-not (summary/>= os ns)
;          (print (summary/status ns))
          (notify-parents n)))))
  (summary-changed-local! [n] (reset! summary-cache nil))
  (verified-summary [n min-summary]
     (let [os @summary-cache
           cs (reset! summary-cache (summarize n))]
;       (swap! *summary-count* dec)
       (when os (util/assert-is (<= (summary/max-reward cs) (summary/max-reward os))))
       (when (summary/>= cs min-summary)
         (let [verified-children (map #(verified-summary (summary/source %) %) (util/unchunk (summary/children cs)))]
           (if (every? identity verified-children)
             (reset! summary-cache (summary/re-child cs verified-children))
             (recur min-summary)))))))




;; Concerns:
;; computing a summary given children
;; When to use cached/fresh
;; verifying that (cached) summary is good enough. --> should be above






