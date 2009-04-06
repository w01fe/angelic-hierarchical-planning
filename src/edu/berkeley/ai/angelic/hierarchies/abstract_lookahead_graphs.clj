(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-graphs
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.graphviz :as graphviz]))


;; Abstract lookahead graphs, which include merge nodes.

; Subsumption is more difficult here, since there's no "rest" of plan to worry about.
; Just ignore it for now, and ignore pessimistic descriptions too.  

; JGraph for visualizaton?

; Should cache by default.

; Like ALT, you should not throw out plans or bad things may happen.

; Do we cache refined nodes or not ?  Seems too tricky.

; Nodes have ref to successors, ref to pred / set of preds.  
; Need backwards connections for searching (main), 
; forwards connections can be cache as before.
; Previous needs to be a reference type

; At some point, collapse Merge-nodes?  Theres a tradeoff...

; To avoid creating duplicate plans, should follow OR-nodes when checking for duplicates,
; don't follow when creating.  

; Don't create OR-nodes for single-refinement.

; To support node methods, must always be ready with state seq? 


; To simplify things, action nodes either have map of action children (if any), or single merge child
; Merge must have action children (if any or final).

;;; Abstract lookahead graphs, Search/Nodes, and internal nodes.
; nil is key for merge.

;; TODO: a way to implement extract-a-solution (or refine potentially suboptimal things...)

; TODO TODO: kill off dead-end fragments.  Just don't return them.
 ; (better than making next-map have weak val refs).

;; TODO: graph minimization somehow? (current method may end up with duplicates, i.e. 
  ; ae, be, ad, cd.

; TODO: enforce consistency, and add assertions back to backwards-pass.

; TODO: cache best predecessor.

;; Note duplicate elimination may look like it's not working, but it's preserving preconds.

; TODO: Can't actually maintain no-forking invariant in general ??

(defstruct abstract-lookahead-graph :class :env :goal :pess-val-type)
(defn- make-alg [env pess-val-type]
  (struct abstract-lookahead-graph ::AbstractLookaheadGraph env (envs/get-goal env) pess-val-type))



(defn add-valuation-metadata [node]
  (with-meta node
   {:pessimistic-valuation (util/sref nil), 
    :optimistic-valuation (util/sref nil)}))	     


(declare add-child!)

(derive ::ALGActionNode ::ALGInternalNode)
(defstruct alg-action-node :class :hla :previous :next-map)

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


(defn alg-node-children [node] (util/sref-get (:next-map node)))

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


;;; Mutating relationships

(defn- add-child! [node child]
  (let [next-map-ref (util/safe-get node :next-map)
	next-map     (util/sref-get next-map-ref)
	key          (:hla child)]
    (util/assert-is (not (contains? next-map key)))
    (when-not key 
      (util/assert-is (= (:class node) ::ALGActionNode))
      (util/assert-is (empty? next-map)))
    (when (and key (= (:class node) ::ALGActionNode))
      (util/assert-is (not (contains? next-map nil))))
    (util/sref-set! next-map-ref (assoc next-map key child))
    child))

(defn- remove-child! [node child]
  (let [next-map-ref (util/safe-get node :next-map)
	next-map     (util/sref-get next-map-ref)
	key          (:hla child)]
    (util/assert-is (contains? next-map key))
    (util/sref-set! next-map-ref (dissoc next-map key))))


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
  (let [prev     (util/sref-get (:previous node)),
	next-map (util/sref-get (:next-map node))]
    (remove-child! prev node)
    (doseq [nxt (vals next-map)] 
      (remove-previous! nxt node))
    [prev next-map]))

(defn- splice-nexts [new-node next-map]
;  (println "SN" (:class new-node))
;  (println "SN" (:class new-node) (count (alg-node-parents new-node)) (count (alg-node-children new-node)))
  (let [new-merge?  (isa? (:class new-node) ::ALGMergeNode)
	post-merge  (get next-map nil)]
;    (println new-merge? (when post-merge true))
    (if (and new-merge? post-merge) ; Prevent sequence of two merges
        (let [merged-nodes (util/sref-get (:previous-set new-node))]
	  (doseq [node merged-nodes]
	    (util/sref-set! (:next-map node) next-map)
	    (add-previous!  post-merge node))
	  post-merge)
      (do (util/sref-set! (:next-map new-node) next-map)
	  (doseq [nxt (vals next-map)]
	    (add-previous! nxt new-node))
	  new-node))))


(defn- get-child [node key]
  (let [next-map-ref (util/safe-get node :next-map)
	next-map     (util/sref-get next-map-ref)]
    (get next-map key)))

; Ensure each plan has a new final node, at least - makes other things easier, hurts graphiness
; TODO: figure out how to improve? 
(defn- make-action-node-seq [prev-node actions]
;  (println (map hla-name actions))
  (util/assert-is (not (empty? actions)))
  (if-let [singleton (util/singleton actions)]
      (make-alg-action-node singleton prev-node)
    (recur (or (get-child prev-node (first actions))
	       (make-alg-action-node (first actions) prev-node))
	   (next actions))))


    

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



(declare alg-optimistic-valuation alg-pessimistic-valuation)
(defmulti compute-alg-optimistic-valuation :class)
(defmulti compute-alg-pessimistic-valuation :class)

(defmethod compute-alg-optimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod compute-alg-pessimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException.)))


(defmethod compute-alg-optimistic-valuation ::ALGActionNode [node]
  (progress-valuation 
   (restrict-valuation (alg-optimistic-valuation (util/sref-get (:previous node)))
		       (hla-hierarchical-preconditions (:hla node)))
   (hla-optimistic-description (:hla node))))

(defmethod compute-alg-pessimistic-valuation ::ALGActionNode [node]
  (progress-valuation 
   (restrict-valuation (alg-pessimistic-valuation (util/sref-get (:previous node)))
		       (hla-hierarchical-preconditions (:hla node)))
   (hla-pessimistic-description (:hla node))))


(defmethod compute-alg-optimistic-valuation ::ALGMergeNode [node]
  (reduce union-valuations (map alg-optimistic-valuation (util/sref-get (:previous-set node)))))

(defmethod compute-alg-pessimistic-valuation ::ALGMergeNode [node]
  (reduce union-valuations (map alg-pessimistic-valuation (util/sref-get (:previous-set node)))))


(defmethod compute-alg-optimistic-valuation ::ALGFinalNode [node]
  (restrict-valuation (alg-optimistic-valuation (:plan node)) (:goal (:alg node))))

(defmethod compute-alg-pessimistic-valuation ::ALGFinalNode [node]
  (restrict-valuation (alg-pessimistic-valuation (:plan node)) (:goal (:alg node))))

  

(defn redundant-hla-seq? "Is hlas already an allowed action seq that connects pre-node to post-node?"
  [pre-node post-next hlas]
  (if (empty? hlas) 
      (when (= (util/sref-get (:next-map pre-node)) post-next) (println "Redundant") true)
    (if-let [nxt (get-child pre-node nil)]
         (recur nxt post-next hlas)
       (when-let [nxt (get-child pre-node (first hlas))]
	 (recur nxt post-next (next hlas))))))
      
(defn replace-node-with-refinements! "Returns final node of refinements" [node hla-seqs]
  (util/assert-is (= ::ALGActionNode (:class node)))
  (if (empty? hla-seqs)  ; TODO: cut out path here...
    (do (util/sref-set! (:optimistic-valuation ^node) *pessimal-valuation*) node)
  (let [[pre-node post-next-map] (cut-action-node node)
	hla-seqs (remove #(redundant-hla-seq? pre-node post-next-map %) hla-seqs)]
    (if (empty? hla-seqs) pre-node
      (let [final-nodes    (doall (map #(make-action-node-seq pre-node %) hla-seqs))]
	(splice-nexts (or (util/singleton final-nodes) (make-alg-merge-node final-nodes)) post-next-map))))))

  


; helpers for caching progression results

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
  (fn [node next-state reward max-gap max-gap-node alg] (:class node)))

(defmethod simple-backwards-pass ::ALGRootNode [node next-state reward max-gap max-gap-node alg]
  (println "SBP Root" (alg-node-name node) next-state reward max-gap)
  (util/assert-is (or (Double/isNaN reward) (= reward 0)))
;  (when (or (Double/isNaN reward) (>= reward 0))
    (util/assert-is (= (valuation-state-reward (alg-optimistic-valuation node) next-state) 0))
    (or max-gap-node []))

(defmethod simple-backwards-pass ::ALGActionNode [node next-state reward max-gap max-gap-node alg]
  (println "SBP Action" (alg-node-name node) next-state reward max-gap)
  (let [val-reward (valuation-state-reward (alg-optimistic-valuation node) next-state)]
;    (util/assert-is (<= val-reward reward))
    (when (> val-reward reward)
      (util/print-debug 3 "Warning: inconsistency at " (alg-node-name node) val-reward reward))
    (when (>= val-reward reward)
      (let [prev-node (util/sref-get (:previous node))
	    regress-pair (regress-state  
					   next-state
					   (alg-optimistic-valuation prev-node)
					   (hla-optimistic-description (:hla node))
					   (alg-optimistic-valuation node))]
	(if (nil? regress-pair) 
	    (do (invalidate-valuations node) nil)
	  (let [[prev-state opt-step-reward] regress-pair
		[prev-s2   pess-step-reward] (or
					      (regress-state 
					       next-state
					       (state->valuation (:pess-val-type alg) prev-state)
					       (hla-pessimistic-description (:hla node))
					       (state->valuation (:pess-val-type alg) next-state))
					      [prev-state Double/NEGATIVE_INFINITY])
		prev-reward (- (max val-reward reward) opt-step-reward)
		gap         (- opt-step-reward pess-step-reward)
		[prev-gap prev-gap-node] (if (and (>= gap max-gap) (not (hla-primitive? (:hla node))))
					   [gap node]
					   [max-gap max-gap-node])
		rec (simple-backwards-pass prev-node prev-state prev-reward prev-gap prev-gap-node alg)]
	    (util/assert-is (= prev-s2 prev-state))
					;	(println "SBP gap " (alg-node-name node) gap (class rec))
	    (cond (isa? (:class rec) ::ALGInternalNode) rec
	    rec                                  (conj rec (:hla node))
	    :else (do (invalidate-valuations node)
		      (recur node next-state reward max-gap max-gap-node alg)))))))))
    
(defmethod simple-backwards-pass ::ALGMergeNode [node next-state reward max-gap max-gap-node alg]
 (println "SBP Merge" (alg-node-name node) next-state reward max-gap)
  (let [val-reward (valuation-state-reward (alg-optimistic-valuation node) next-state)]
;    (util/assert-is (<= val-reward reward))
    (when (> val-reward reward)
      (util/print-debug 3 "Warning: inconsistency at " (alg-node-name node) val-reward reward))
    (when (>= val-reward reward)
      (or (when-first [prev-node
		       (filter #(>= (valuation-state-reward (alg-optimistic-valuation %) next-state) reward)
			       (util/sref-get (:previous-set node)))]
	    (simple-backwards-pass prev-node next-state reward max-gap max-gap-node alg))
	  (do (invalidate-valuations node)
	      (recur node next-state reward max-gap max-gap-node alg))))))

(defn drive-simple-backwards-pass [node]
  (let [alg (:alg node)
	pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(loop []
	  (when-let [[state rew] (valuation-max-reward-state (alg-optimistic-valuation node))]
	    (println "Driving " state rew)
	    (or (util/sref-set! pass-cache (simple-backwards-pass (:plan node) state rew 0 nil alg))
		(do  (invalidate-valuations node)
		     (recur))))))))

;TODO:  Functions needed: valuation-state-reward, regress-optimistic-state, regress-pessimistic-state, state->valuation, extract-a-best-state.  


;;; Constructing initial ALG nodes

(defn make-initial-alg-node  
  ([initial-node]
     (make-initial-alg-node 
      (hla-default-optimistic-valuation-type initial-node) 
      (hla-default-pessimistic-valuation-type initial-node)
      initial-node))
  ([opt-valuation-class pess-valuation-class initial-node]
     (let [initial-plan (list initial-node) 
	   env (hla-environment (first initial-plan)), 
	   alg (make-alg env pess-valuation-class)]
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
;    (println "IR " (class bp))
    (when bp
      (util/assert-is (isa? (:class bp) ::ALGActionNode))
      (util/print-debug 3 "Refining at " (alg-node-name bp))
      (util/sref-up! search/*ref-counter* inc)
      (let [refs (hla-immediate-refinements (:hla bp) (alg-optimistic-valuation (util/sref-get (:previous bp))))
	    final (replace-node-with-refinements! bp refs)]
	(util/print-debug 3  "Got refinements " (for [r refs] (map hla-name r)))
	[(make-alg-final-node (:alg node)
	  (if (empty? (util/sref-get (:next-map final))) final (:plan node)))]))))


(defmethod search/primitive-refinement ::ALGFinalNode [node]
;  (println "PR " (System/identityHashCode node))
  (let [bp (drive-simple-backwards-pass node)]
;    (println "PR " (class bp))
    (when (and bp (not (isa? (:class bp) ::ALGActionNode)))
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
  (graphviz/graphviz 
   (find-alg-root node)
   identity
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation n))
	    (valuation-max-reward (alg-optimistic-valuation n))])
   (fn [n] 
     (for [nxt (vals (util/sref-get (:next-map n)))]
       [(alg-node-name nxt)
	nxt]))))
   
(defn graphviz-alg2 [node]
  "TODO: identify source of node, etc."
  (graphviz/write-graphviz "/tmp/alg.pdf"
   (find-alg-root node)
   identity
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation n))
	    (valuation-max-reward (alg-optimistic-valuation n))])
   (fn [n] 
     (for [nxt (vals (util/sref-get (:next-map n)))]
       [(alg-node-name nxt)
	nxt])))
  (util/sh "open" "-a" "Skim" "/tmp/alg.pdf"))

  
(comment 
  (a-star-search (alg-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 3 3 [[1 1]] [2 0] true [0 2])))))

(binding [*debug-level* 3] (interactive-search (alg-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))))))
  )



