(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-graphs
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.graphviz :as graphviz]))


;; Abstract lookahead graphs, which include merge nodes.

; Subsumption is more difficult here, since there's no "rest" of plan to worry about.
; Just ignore it for now, and ignore pessimistic descriptions too.  

; We extract state sequenes going backwards since we need to make consistent choices at or-nodes (merges)

; Like ALT, you should not throw out plans or bad things may happen.

;;; Abstract lookahead graphs, Search/Nodes, and internal nodes.
; nil is key for merge.

;; TODO: a way to implement extract-a-solution (or refine potentially suboptimal things...)

; TODO: cache best predecessor.

;; Note duplicate elimination may look like it's not working, but it's preserving preconds.

; TODO: Incremental HLA refinement?


; Take parameters 
  ; type of graph to build
  ; search strategy to use (incl. valuation tricks)?
  ; subsumption improvement strategy (merge-opt, pess, ...)

; When you split, you have to be careful, or you could find suboptimal solutions ...
 ; solution; generate new search node every time you increase the cost bound.

(defstruct abstract-lookahead-graph :class :env :goal :split-set)
(defn- make-alg [env split-set]
  (struct abstract-lookahead-graph ::AbstractLookaheadGraph env (envs/get-goal env) split-set))



(defn add-valuation-metadata [node]
  (with-meta node
   {:pessimistic-valuation (util/sref nil), 
    :optimistic-valuation (util/sref nil)}))	     


(declare add-child!)

(derive ::ALGActionNode ::ALGInternalNode)
(defstruct alg-action-node :class :hla :previous :next-map)
; next-map is a map from hlas to (mutable) weak-ref-seq objects.

(defn make-alg-action-node [hla previous-node] 
  (add-child! previous-node
   (add-valuation-metadata
    (struct alg-action-node ::ALGActionNode hla (util/sref previous-node) (util/sref {})))))


(derive ::ALGMergeNode ::ALGInternalNode)
(derive ::ALGRootNode ::ALGMergeNode)
(defstruct alg-merge-node :class :previous-set :next-map)

(defn make-alg-root-node [opt-val pess-val] 
  (let [n (add-valuation-metadata
	   (struct alg-merge-node ::ALGRootNode (util/sref #{}) (util/sref {})))]
    (util/sref-set! (:optimistic-valuation ^n) opt-val)
    (util/sref-set! (:pessimistic-valuation ^n) pess-val) 
    n))


(defn make-alg-merge-node [previous-set]
  (let [n (add-valuation-metadata
	   (struct alg-merge-node ::ALGMergeNode (util/sref (util/to-set previous-set)) (util/sref {})))]
    (doseq [prev previous-set] (add-child! prev n))
    n))


(derive ::ALGFinalNode ::search/Node)
(defstruct alg-final-node :class :alg :plan :pass-cache)
(defn make-alg-final-node [alg plan]
  (add-valuation-metadata
   (struct alg-final-node ::ALGFinalNode alg plan (util/sref nil))))



;;; Internal node methods.


; Helpers for (mostly) debugging and visualizing

(defmulti alg-node-parents :class)
(defmethod alg-node-parents ::ALGRootNode [node] nil)
(defmethod alg-node-parents ::ALGMergeNode [node] (util/sref-get (:previous-set node)))
(defmethod alg-node-parents ::ALGActionNode [node] [(util/sref-get (:previous node))])

(defn find-alg-root [final-node]
  (last (util/iterate-while #(first (alg-node-parents %)) (:plan final-node))))

(defmulti alg-node-name :class)
(defmethod alg-node-name ::ALGRootNode [node] "ROOT")
(defmethod alg-node-name ::ALGActionNode [node] (hla-name (:hla node))) ;;(str (hla-name (:hla node)) "-" (System/identityHashCode node)))
(defmethod alg-node-name ::ALGMergeNode [node]  "Merge");(str "Merge-" (System/identityHashCode node)))


; Helpers for working with and modifying graph structure

(defn- get-children 
  ([node]
     (apply concat
       (for [k (keys (util/sref-get (util/safe-get node :next-map)))]
	 (get-children node k))))
  ([node key]
     (let [next-map-ref (util/safe-get node :next-map)
	   next-map     (util/sref-get next-map-ref)]
       (when-let [wrs (get next-map key)]
	 (util/weak-ref-seq wrs)))))

(defn- add-child! [node child]
  (let [next-map-ref (util/safe-get node :next-map)
	next-map     (util/sref-get next-map-ref)
	key          (:hla child)
	old-wrs      (get next-map key)
	wrs          (or old-wrs
			 (let [wrs (util/make-weak-ref-seq)]
			   (util/sref-set! next-map-ref (assoc next-map key wrs))
			   wrs))]
;    (util/assert-is (nil? old-wrs))
;    (when-not key 
;      (util/assert-is (= (:class node) ::ALGActionNode))
;      (util/assert-is (empty? next-map)))
;    (when (and key (= (:class node) ::ALGActionNode))
;      (util/assert-is (not (contains? next-map nil))))
    (util/weak-ref-seq-add! wrs child)
    child))


(defmulti add-previous! (fn [node new-prev] (:class node)))

(defmethod add-previous! ::ALGActionNode [node new-prev]
  (let [prev-ref (:previous node)]
    (util/assert-is (nil? (util/sref-get prev-ref)))
    (util/sref-set! prev-ref new-prev)))

(defmethod add-previous! ::ALGMergeNode [node new-prev]
  (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (util/sref-set! prev-ref (conj prev-set new-prev))))


(defmulti remove-previous! (fn [node old-prev] (:class node)))

(defmethod remove-previous! ::ALGActionNode [node old-prev]
  (let [prev-ref (:previous node)]
    (util/assert-is (identical? (util/sref-get prev-ref) old-prev))
    (util/sref-set! prev-ref nil)))

(defmethod remove-previous! ::ALGMergeNode [node old-prev]
  (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (util/assert-is (contains? prev-set old-prev))
    (util/sref-set! prev-ref (disj prev-set old-prev))))


(defn- cut-action-node [node]
  (util/assert-is (isa? (:class node) ::ALGActionNode))
  (doseq [nxt (get-children node)] 
    (remove-previous! nxt node))
  [(util/sref-get (:previous node)) (util/sref-get (:next-map node))])


(defn- splice-nexts [new-node next-map]
;  (println "SN" (:class new-node))
;  (println "SN" (:class new-node) (count (alg-node-parents new-node)) (count (alg-node-children new-node)))
  (do (util/sref-set! (:next-map new-node) next-map)
      (doseq [nxt (get-children new-node)]
	(add-previous! nxt new-node))
      new-node))

(comment ; old version, merged everything - slows things down.
(defn- splice-nexts [new-node next-map]
;  (println "SN" (:class new-node))
;  (println "SN" (:class new-node) (count (alg-node-parents new-node)) (count (alg-node-children new-node)))
  (let [new-merge?  (isa? (:class new-node) ::ALGMergeNode)
	post-merge  (first (util/weak-ref-seq (get next-map nil)))]  ; TODO
;    (println new-merge? (when post-merge true))
    (if (and new-merge? post-merge) ; Prevent sequence of two merges
        (let [merged-nodes (util/sref-get (:previous-set new-node))]
	  (doseq [node merged-nodes]
	    (util/sref-set! (:next-map node) next-map)
	    (add-previous!  post-merge node))
	  post-merge)
      (do (util/sref-set! (:next-map new-node) next-map)
	  (doseq [nxt (get-children new-node)]
	    (add-previous! nxt new-node))
	  new-node))))
  )


; Ensure each plan has a new final node, at least - makes other things easier, hurts graphiness
; TODO: figure out how to improve? 
(defn- make-action-node-seq [prev-node actions]
;  (println (map hla-name actions))
  (util/assert-is (not (empty? actions)))
  (if-let [singleton (util/singleton actions)]
      (make-alg-action-node singleton prev-node)
    (recur (or (first (get-children prev-node (first actions))) ;; TODO: wrong with multiple children?
	       (make-alg-action-node (first actions) prev-node))
	   (next actions))))

      


;;; Computing valuations, etc.

(declare alg-optimistic-valuation alg-pessimistic-valuation)
(defmulti compute-alg-optimistic-valuation :class)
(defmulti compute-alg-pessimistic-valuation :class)

(defmethod compute-alg-optimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod compute-alg-pessimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException.)))


(defmethod compute-alg-optimistic-valuation ::ALGActionNode opt-action [node]
;  (println "Progress action " (hla-name (:hla node)))
  (let [previous (util/sref-get (:previous node))]
    (if (nil? previous)
        *pessimal-valuation*
      (progress-valuation 
       (restrict-valuation (alg-optimistic-valuation previous)
			   (hla-hierarchical-preconditions (:hla node)))
       (hla-optimistic-description (:hla node))))))

(defmethod compute-alg-pessimistic-valuation ::ALGActionNode pess-action [node]
  (let [previous (util/sref-get (:previous node))]
    (if (nil? previous)
        *pessimal-valuation*
      (progress-valuation 
       (restrict-valuation (alg-pessimistic-valuation previous)
			   (hla-hierarchical-preconditions (:hla node)))
       (hla-pessimistic-description (:hla node))))))


(defmethod compute-alg-optimistic-valuation ::ALGMergeNode opt-merge [node]
;  (println "Progress merge ")
  (let [previous-set (util/sref-get (:previous-set node))
	pruned-set   (reduce (fn [s e] (if (empty-valuation? (alg-optimistic-valuation e)) (disj s e) s))
			     previous-set previous-set)]
    (util/sref-set! (:previous-set node) pruned-set)
    (if (empty? pruned-set) *pessimal-valuation*
      (reduce union-valuations 
	      (for [n pruned-set]
		(add-clause-metadata (alg-optimistic-valuation n) {:source-node n}))))))
	      ;(map alg-optimistic-valuation pruned-set)))))

(defmethod compute-alg-pessimistic-valuation ::ALGMergeNode pess-merge [node]
  (let [previous-set (util/sref-get (:previous-set node))]
    (if (empty? previous-set) *pessimal-valuation*
      (reduce union-valuations (map alg-pessimistic-valuation previous-set)))))


(defmethod compute-alg-optimistic-valuation ::ALGFinalNode opt-final [node]
  (restrict-valuation (alg-optimistic-valuation (:plan node)) (:goal (:alg node))))

(defmethod compute-alg-pessimistic-valuation ::ALGFinalNode pess-final [node]
  (restrict-valuation (alg-pessimistic-valuation (:plan node)) (:goal (:alg node))))

 
(defn alg-optimistic-valuation [node]
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *op-counter* inc)
	      (compute-alg-optimistic-valuation node))))))

(defn alg-pessimistic-valuation [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *pp-counter* inc)
	      (compute-alg-pessimistic-valuation node))))))


(defn invalidate-valuations [node]
  (util/sref-set! (:optimistic-valuation ^node) nil)
  (util/sref-set! (:pessimistic-valuation ^node) nil)
  nil)



;; Simple backwards-pass

(defmulti simple-backwards-pass
  "Simple-backwards-pass takes [node next-state reward max-gap max-gap-node],
   and returns either a node to refine, an optimal primitive refinement, or 
   nil (indicating that no plan exists to next-state that achieves reward (>)= reward"
  (fn [node next-state next-clause reward max-gap max-gap-node alg] (:class node)))

(defmethod simple-backwards-pass ::ALGRootNode sbp-root [node next-state next-clause reward max-gap max-gap-node alg]
;  (println "SBP Root" (alg-node-name node) next-state reward max-gap)
  (util/assert-is (or (Double/isNaN reward) (= reward 0)))
;  (when (or (Double/isNaN reward) (>= reward 0))
    (util/assert-is (= (valuation-state-reward (alg-optimistic-valuation node) next-state) 0))
    (or max-gap-node []))

(defmethod simple-backwards-pass ::ALGActionNode sbp-action [node next-state next-clause reward max-gap max-gap-node alg]
  (util/timeout)
 ;   (when next-clause (util/assert-is (clause-includes-state? next-clause next-state)))
  (let [prev-node (util/sref-get (:previous node))
	prev-val (alg-optimistic-valuation prev-node)]
    (let [[prev-state step-reward pre-reward prev-clause]
	  (or (regress-state-hinted next-state prev-val (hla-optimistic-description (:hla node)) 
				    (alg-optimistic-valuation node) next-clause)
	      [:dummy Double/NEGATIVE_INFINITY Double/NEGATIVE_INFINITY])]
      (if (>= (+ pre-reward step-reward) reward)
	  (let [rec (simple-backwards-pass prev-node prev-state prev-clause pre-reward 0 
					   (if (hla-primitive? (:hla node)) max-gap-node node) alg)]
	    (cond (isa? (:class rec) ::ALGInternalNode) 
		    rec
		  rec   
		    (conj rec (:hla node))
		  :else                            
		    (recur node next-state nil reward max-gap max-gap-node alg)))
	(invalidate-valuations node)))))


(comment

  (let [val-reward (valuation-state-reward (alg-optimistic-valuation node) next-state)]
;  (println "SBP Action" (alg-node-name node) next-state reward val-reward max-gap (:class (alg-optimistic-valuation node)) (:class (alg-optimistic-valuation (util/sref-get (:previous node)))))
;    (util/assert-is (<= val-reward reward))
    (when (> val-reward reward)
      (util/print-debug 3 "Warning: inconsistency at " (alg-node-name node) val-reward reward))
    (when (>= val-reward reward)
      (let [prev-node (util/sref-get (:previous node))
	    regress-pair (regress-state    next-state
					   (alg-optimistic-valuation prev-node)
					   (hla-optimistic-description (:hla node))
					   (alg-optimistic-valuation node))]
;	(println "Regress to " regress-pair)
	(if (nil? regress-pair) 
	    (do (invalidate-valuations node) nil)
	  (let [[prev-state opt-step-reward] regress-pair
		[prev-s2   pess-step-reward] (or [prev-state opt-step-reward]) ;; TODO: put back
					     ; (regress-clause-state 
					     ;  next-state
					     ;  (state->clause prev-state)
					     ;  (hla-pessimistic-description (:hla node))
					     ;  nil)
					     ; [prev-state Double/NEGATIVE_INFINITY])
		prev-reward (- (max val-reward reward) opt-step-reward)
		gap         (- opt-step-reward pess-step-reward)
		[prev-gap prev-gap-node] (if (and (>= gap max-gap) (not (hla-primitive? (:hla node))))
					   [gap node]
					   [max-gap max-gap-node])
		rec (simple-backwards-pass prev-node prev-state nil prev-reward prev-gap prev-gap-node alg)]
	    ;(util/assert-is (= prev-s2 prev-state))
	;	(println "SBP gap " (alg-node-name node) gap (class rec))
	    (cond (isa? (:class rec) ::ALGInternalNode) rec
	    rec                                  (conj rec (:hla node))
	    :else (do (invalidate-valuations node)
		      (recur node next-state next-clause reward max-gap max-gap-node alg)))))))))
    
;(def *ov* )
(defmethod simple-backwards-pass ::ALGMergeNode sbp-merge [node next-state next-clause reward max-gap max-gap-node alg]
;  (println "SBP-merge")
 ; (when next-clause (util/assert-is (clause-includes-state? next-clause next-state)))
  (if next-clause
      (or 
        (when-let [prev-node (get ^next-clause :source-node)]
	  (when (contains? (util/sref-get (:previous-set node)) prev-node)
	    (when-let [[clause val-reward] (valuation-clause-reward (alg-optimistic-valuation prev-node) next-clause)]
	      (when (>= val-reward reward); (println "GO")
;		(print ",")
		(simple-backwards-pass prev-node next-state clause reward max-gap max-gap-node alg)))))
	(recur node next-state nil reward max-gap max-gap-node alg))
    (loop [good-preds
	       (seq (filter identity
		     (for [prev-node (util/sref-get (:previous-set node))]
		       (let [prev-val (alg-optimistic-valuation prev-node)]
			 (if (isa? (:class prev-val) :edu.berkeley.ai.angelic/PropositionalValuation)
			     (when-let [[prev-clause prev-rew] (valuation-state-clause-reward prev-val next-state)]
			       (when (>= prev-rew reward)
				 [prev-node prev-clause prev-rew]))
			   (let [prev-rew (valuation-state-reward prev-val next-state)]
			     (when (>= prev-rew reward)
			       [prev-node nil prev-rew])))))))]
      (if good-preds 
	  (let [[prev-node prev-clause prev-rew] (first good-preds)]
	    (or (simple-backwards-pass prev-node next-state prev-clause reward max-gap max-gap-node alg)
		(recur (next good-preds))))
	(invalidate-valuations node)))))
		      
     
(comment	

  (let [val-reward (valuation-state-reward (alg-optimistic-valuation node) next-state)]
;    (println "SBP Merge" (alg-node-name node) next-state reward val-reward max-gap)
;    (def *ov* (alg-optimistic-valuation node))
;    (util/assert-is (<= val-reward reward))
    (when (> val-reward reward)
      (util/print-debug 3 "Warning: inconsistency at " (alg-node-name node) val-reward reward))
    (when (>= val-reward reward)
      (or (when-first [prev-node
		       (filter #(>= (valuation-state-reward (alg-optimistic-valuation %) next-state) reward)
			       (util/sref-get (:previous-set node)))]
	    (simple-backwards-pass prev-node next-state nil reward max-gap max-gap-node alg))
	  (do (invalidate-valuations node)
	      (recur node next-state next-clause reward max-gap max-gap-node alg)))))
  )

(defn get-max-reward-state-and-clause [v]
  (if (isa? (:class v) :edu.berkeley.ai.angelic/PropositionalValuation)
      (when-let [[clause rew] (valuation-max-reward-clause v)]
	[(minimal-clause-state clause) rew clause])
    (valuation-max-reward-state v)))

(defn drive-simple-backwards-pass [node]
;  (println "\n\n\n DRIVE")
  (let [alg (:alg node)
	pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(util/sref-set! pass-cache
	  (or
	    (when-let [[state rew clause] (get-max-reward-state-and-clause (alg-optimistic-valuation node))]
	      (or (simple-backwards-pass (:plan node) state clause rew 0 nil alg)
		  (do (invalidate-valuations node) nil)))
	    :fail)))))

;TODO:  Functions needed: valuation-state-reward, regress-optimistic-state, regress-pessimistic-state, state->valuation, extract-a-best-state.  


;;; Constructing initial ALG nodes

(defn make-initial-alg-node  
  ([initial-node]
     (make-initial-alg-node initial-node #{}))
  ([initial-node split-set]
     (make-initial-alg-node 
      (hla-default-optimistic-valuation-type initial-node) 
      (hla-default-pessimistic-valuation-type initial-node)
      initial-node split-set))
  ([opt-valuation-class pess-valuation-class initial-node split-set]
     (let [initial-plan (list initial-node) 
	   env (hla-environment (first initial-plan)), 
	   alg (make-alg env split-set)]
       (make-alg-final-node alg
         (make-action-node-seq 
	  (make-alg-root-node 
	   (state->valuation opt-valuation-class (envs/get-initial-state env))
	   (state->valuation pess-valuation-class (envs/get-initial-state env)))
	  initial-plan)))))

(defn alg-node [& args] (apply make-initial-alg-node args))





;;; Node methods 

(defmethod search/reroot-at-node ::ALGFinalNode [node & args]
  (throw (UnsupportedOperationException.)))

(defmethod search/node-environment   ::ALGFinalNode [node] 
  (util/safe-get-in node [:alg :env]))

(defmethod search/node-state         ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod search/upper-reward-bound ::ALGFinalNode [node] 
  (valuation-max-reward (alg-optimistic-valuation node)))

(defmethod search/lower-reward-bound ::ALGFinalNode [node] 
  (valuation-max-reward (alg-pessimistic-valuation node)))

(defmethod search/reward-so-far ::ALGFinalNode [node] 0)

(defmethod search/immediate-refinements ::ALGFinalNode [node] 
  (util/timeout)
;  (println "IR " (System/identityHashCode node))
  (let [bp (drive-simple-backwards-pass node)]
    (util/assert-is (identity bp))
    (cond (= bp :fail)
 	    (when (> (valuation-max-reward (alg-optimistic-valuation node)) Double/NEGATIVE_INFINITY)
	      [(make-alg-final-node (:alg node) (:plan node))])
	  (not (isa? (:class bp) ::ALGActionNode))
	    (do (println "Warning: trying to refine optimal node")
		nil)
	  :else 
	    (let [hla    (:hla bp)
		  split? (contains? (util/safe-get-in node [:alg :split-set]) (first (hla-name hla)))
		  final? (empty? (get-children bp))
		  refs   (hla-immediate-refinements (:hla bp) (alg-optimistic-valuation (util/sref-get (:previous bp))))
		  [pre-node post-next-map] (cut-action-node bp)
		  final-nodes (doall (map #(make-action-node-seq pre-node %) refs))]
	      (when split? (util/assert-is (identity final?)))
	      (util/print-debug 3 "Refining at " (alg-node-name bp) ";\nGot refinements " (for [r refs] (map hla-name r)))
	      (util/sref-up! search/*ref-counter* inc)
	      (if split? 
		  (map #(make-alg-final-node (:alg node) %) final-nodes)
		(when (not (and final? (empty? final-nodes)))
		  (let [spliced (splice-nexts (or (util/singleton final-nodes) (make-alg-merge-node final-nodes)) 
					      post-next-map)]
		    [(make-alg-final-node (:alg node) (if final? spliced (:plan node)))])))))))


(defmethod search/primitive-refinement ::ALGFinalNode [node]
;  (println "PR " (System/identityHashCode node))
  (let [bp (drive-simple-backwards-pass node)]
    (util/assert-is (identity bp))
;    (println "PR " (class bp))
    (when (and (not (= bp :fail)) (not (isa? (:class bp) ::ALGActionNode)))
      [(remove #(= % :noop) (map hla-primitive bp))
       (search/upper-reward-bound node)])))

(defmethod search/extract-optimal-solution ::ALGFinalNode [node] 
  (search/primitive-refinement node))



(defmethod search/node-str ::ALGFinalNode [node] 
  "ALG")

(defmethod search/node-first-action ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod search/node-plan-length ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))




(defn graphviz-alg [node]
  "TODO: identify source of node, etc."
  (dotimes [_ 5] (util/force-gc))
  (graphviz/graphviz 
   (find-alg-root node)
   identity
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation n))
	    (valuation-max-reward (alg-optimistic-valuation n))])
   (fn [n] 
     (for [nxt (get-children n)]
       [(alg-node-name nxt)
	nxt]))))
   
(defn graphviz-alg2 [node]
  "TODO: identify source of node, etc."
  (dotimes [_ 5] (util/force-gc))
  (graphviz/write-graphviz "/tmp/alg.pdf"
   (find-alg-root node)
   identity
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation n))
	    (valuation-max-reward (alg-optimistic-valuation n))])
   (fn [n] 
     (for [nxt (get-children n)]
       [(alg-node-name nxt)
	nxt])))
  (util/sh "open" "-a" "Skim" "/tmp/alg.pdf"))

  
(comment 
  (a-star-search (alg-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 3 3 [[1 1]] [2 0] true [0 2])))))

(binding [*debug-level* 3] (interactive-search (alg-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))))))
  )







(comment

(defmulti replace-previous! (fn [node old-prev new-prev] (:class node)))

(defmethod replace-previous! ::ALGActionNode [node old-prev new-prev]
  (let [prev-ref (:previous node)]
    (util/assert-is (identical? (util/sref-get prev-ref) old-prev))
    (util/sref-set! prev-ref new-prev)))

(defmethod replace-previous! ::ALGMergeNode [node old-prev new-prev]
  (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (util/assert-is (contains? prev-set old-prev))
    (util/sref-set! prev-ref (conj (disj prev-set old-prev) new-prev))))

(defn replace-previouses! [node old-prev new-prevs]
  (util/assert-is (= (:class node) ::ALGMergeNode))
 (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (util/assert-is (contains? prev-set old-prev))
    (util/sref-set! prev-ref (into (disj prev-set old-prev) new-prevs))))



;(defn redundant-hla-seq? "Is hlas already an allowed action seq that connects pre-node to post-node?"
;  [pre-node post-next hlas]
;  (if (empty? hlas) 
;      (when (= (util/sref-get (:next-map pre-node)) post-next) (println "Redundant") true)
;    (if-let [nxt (first (get-children pre-node nil))] ;; TODO: wrong with multi children.
;         (recur nxt post-next hlas)
;       (when-let [nxt (first (get-children pre-node (first hlas)))] ;TODO
;	 (recur nxt post-next (next hlas))))))
)