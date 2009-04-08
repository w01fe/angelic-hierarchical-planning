(ns edu.berkeley.ai.angelic.hierarchies.-graphs
  (:import java.util HashMap)
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.graphviz :as graphviz]))

;; Clause graphs, like ALGs, which combine the benefits of ALTs and ALGs.

; TODO: caching?

; TODO: detect subsumption among children, use to refine subsumption lattice.
; TODO: considering detecting subsumption among immediate refinements
  ; Gets most of possible ALG+subsumption win back
  ; And if keep track of "dopplegangers/split buddies", can get it all ... if we want it.


; TODO: double hashing - clause first, then rest-plan ?? allows reusing subsumption rels.
  ; or just subsumption cache?  Think about sharing here.  Also allows sloppy hierarchy,

; Spse we have node with [a b] to go
; We are at node with [c b] to go, c refines to ..

; Do we do this in mutable or immutable style, or some combination?
 ; Leave it open for now?

;; Nodes have many rest-plans ........

; TODO: treemap-based pred and child queues. ?

; TODO: how do we even get subsumption ??
 ; When we shift-down, need it too -- would be easier if we got by-effect results. 
  ; What if we get a clause subsumed by nobody ??

; In simplest case, no subsumption -- when we generate a new clause, we start out fresh;
 ; As oppesed to in graph, where we start by updating just previous best plan with this clause.
  ; (and all others).  

; OK, this will work, but consistency is difficult.  Can't do it at edge level, since edge is shared
  ; (and we don't know how to distrubute the extra cost properly).  Or port- or node level.  Forget it for now?
 ; Just do it once, when you do the refinement.  
 ; Only time you do increase is when encountering intermediate nodes when generating refinement.

; First do simplest version, no subsumption detection at all, shifting down, anything.

; TODO: problem with extraction with sub -- multiple paths to single state?

; Use goal-noop.  Even better, special "finish" action.  OK.

; Problem: regressing states, must know final clause.
  ; what if we do get a better reward, from a different outcome clause?  Do we really care? 
  ; This is optimistic, that's not allowed! Well, it is, but not in *that* way ?

(derive ::CGRootNode ::CGNode)

(defstruct cg-node :class :clause :plan-suffix :max-in-reward 
	   :max-sub-reward :sub-node-map :pre-edges :post-edges)

(defn- make-cg-node [clause plan-suffix]
  (struct cg-node ::CGNode clause plan-suffix (util/sref Double/NEGATIVE_INFINITY) 
	  :later :later ;(util/sref Double/NEGATIVE_INFINITY) (util/sref {}) 
	  (util/sref #{}) (util/sref {})))

(defn- make-cg-root-node [clause plan-suffix]
  (struct cg-node ::CGRootNode clause plan-suffix (util/sref 0)
	  :root :root :root (util/sref {})))


(defstruct cg-edge :class :source-node :hla :opt-desc :pess-desc :clause-map :in-reward :suffix-set)

(defn- make-cg-edge [source-node hla]
  (let [od (hla-optimistic-description hla)] 
    (struct cg-edge ::CGEdge source-node hla 
	    od (hla-pessimistic-description hla)
	    (progress-clause (:clause source-node) od)  ; TODO: detect subsumption chains.
	    (util/sref Double/NEGATIVE_INFINITY))))


(defstruct clause-graph :class :node-map)
(defn- make-clause-graph [env]
  (struct clause-graph ::ClauseGraph env (envs/get-goal env) (HashMap.)))

(declare add-plan!)
(defn make-clause-graph [initial-node]
  (let [initial-plan [initial-node (hla-finish-hla initial-node)]
	root-clause  (state->clause (get-initial-state (hla-environment initial-node)))
	root-node    (make-cg-root-node root-clause initial-plan)
	node-map     (HashMap. {[root-clause initial-plan]})]
    (add-plan! node-map root-node initial-plan)
    (struct clause-graph ::ClauseGraph node-map))) 
    

;;; Helper functions

(defn- connect-cg-node [#^HashMap node-map edge clause plan-suffix]
  (let [pair [clause plan-suffix]
	node (or (.get node-map pair)
		 (let [n (make-cg-node clause plan-suffix)]
		   (.put node-map pair n)
		   n))
	pre-edges-ref (:pre-edges node)]
    (util/assert-is (not (contains? (util/sref-get pre-edges-ref) edge)))
    (util/sref-up! pre-edges-ref conj edge)
    node))

(defn- get-cg-node [#^HashMap node-map clause plan-suffix]
  (util/safe-get node-map [clause plan-suffix]))
		 
(defn- get-outgoing-edge [node hla]
  (or (get (sref-get (:post-edges cg-node)) hla)
      (let [edge (make-cg-edge node node hla)]
	(sref-up! (:post-edges cg-node) assoc hla edge))))

(defn add-edge! 
  "Add/extend this edge to node, or increase its reward, returning a seq of nodes whose reward increased in the process."
  [node-map node plan-suffix]
  (let [edge (get-outgoing-edge node (first plan-suffix))
	reward (util/sref-get (:max-in-reward node))]
    (concat
     (when (> reward (sref-get (:in-reward edge)))
       (util/sref-set! (:in-reward edge) reward)
       (doall
         (for [[clause step-rew] (:clause-map edge)
	       suffix            (util/sref-get (:suffix-set edge))
	       :let [tot-rew   (+ reward step-rew)
		     next-node (get-cg-node node-map clause suffix)
		     next-rew  (util/sref-get (:max-in-reward next-node))]
	       :when (> tot-rew next-rew)]
	   (do (util/sref-set! (:max-in-reward next-node) tot-rew)
	       next-node))))
     (when (not (contains? (util/sref-get (:suffix-set edge)) (next plan-suffix)))
       (util/sref-up! (:suffix-set edge) conj (next plan-suffix))
       (doall 
	(for [[clause step-rew] (:clause-map edge)
	      :let [tot-rew (+ reward step-rew)
		    next-node (connect-cg-node node-map edge clause (next plan-suffix))
		    next-rew  (util/sref-get (:max-in-reward next-node))]
	      :when (> tot-rew next-rew)]
	  (do (util/sref-set! (:max-in-reward next-node) tot-rew)
	      next-node)))))))
	 

(defn add-plan! [node-map root-node plan-suffix]
  (loop [nodes [root-node] plan-suffix (seq plan-suffix)]
    (when (and (seq nodes) plan-suffix)
      (recur 
       (distinct (doall (mapcat #(add-edge! node-map % plan-suffix) nodes)))
       (next plan-suffix)))))

(defn refine-cg-edge! [node-map edge suffix]
  (util/assert-is (contains? (sref-get (:suffix-set edge)) suffix))
  (util/sref-up! (:suffix-set edge) disj suffix)
  (doseq [[clause rew] (:clause-map edge)]
    (let [node      (get-cg-node node-map clause suffix)
	  pre-edges (:pre-edges node)]
      (util/assert-is (contains? (sref-get pre-edges) edge))
      (util/sref-up! pre-edges disj edge)))
  (let [source-node (:source-node edge)
	clause      (:clause source-node)
	refs        (hla-immediate-refinements (:hla edge) (make-dnf-valuation ::DNFValuation {clause 0}))]
    (doseq [ref refs]
      (add-plan! node-map source-node (concat ref suffix)))))




(defn- cg-node-best-incoming-edge [node]
  (let [pair
	(first-maximal-element second
	  (cons [:dummy Double\NEGATIVE_INFINITY]
		(for [edge (sref-get (:pre-edges node))]
		  [edge 
		   (+ (sref-get      (:in-reward edge))
		      (util/safe-get (:clause-map edge) (:clause node)))])))]
    (util/sref-set! (:max-in-reward node) (second pair))
    pair))

(defn cg-edge-regress-state [edge final-clause state]
  "Returns state opt-rew pess-rew"
  (let [[final-clause rew] (util/safe-get (:clause-map edge) final-clause)
	prev-state         (minimal-clause-state (util/safe-get ^final-clause :pre-clause))
	[pess-state pess-rew] (or 
			       (regress-clause-state 
			        state
				(state->clause prev-state)
				(:pess-desc edge)
				(state->clause state))
			       [prev-state Double/NEGATIVE_INFINITY])]
    (util/assert-is (= pess-state prev-state))
    [prev-state rew pess-rew])) 

  

;;; Searching

(defmulti simple-cg-backwards-pass
  "Simple-backwards-pass takes [node next-state reward max-gap max-gap-node],
   and returns either a node to refine, an optimal primitive refinement, or 
   nil (indicating that no plan exists to next-state that achieves reward (>)= reward"
  (fn [node next-state rest-reward target-reward max-gap max-gap-node ] (:class node)))

(defmethod simple-cg-backwards-pass ::CGRootNode [node next-state rest-reward target-reward max-gap max-gap-node alg]
  (util/assert-is (= rest-reward target-reward))
  (util/assert-is (clause-includes-state? (:clause node) next-state))
  (or max-gap-node []))


(defmethod simple-cg-backwards-pass ::CGNode [node next-state rest-reward target-reward max-gap max-gap-node]
  (util/timeout)
  (util/assert-is (>= (+ (util/sref-get (:max-in-reward node)) rest-reward) target-reward))
  (let [[best-edge best-reward] (cg-node-best-incoming-edge node)]
    (when (>= (+ best-reward rest-reward) target-reward)
      (let [[prev-state opt-rew pess-rew] (cg-edge-regress-state edge (:clause node) next-state)
	    gap                           (- opt-rew pess-rew)
	    prev-node            (:source-node edge)
	    rec                  (simple-cg-backwards-pass prev-node prev-state (+ opt-rew rest-rew)
							   target-reward (max gap max-gap)
							   (if (and (>= gap max-gap) (not (hla-primitive? (:hla edge))))
							     [:refine edge (:plan-suffix node)] max-gap-node))]
	(cond (= (first rec) :refine) rec
	      rec                     (conj rec (:hla edge))
	      :else                   (do (util/sref-set! (:in-reward edge) 
							  (util/sref-get (:max-in-reward prev-node)))
					  (recur node next-state rest-reward target-reward max-gap max-gap-node)))))))

(defn solve-cg [cg]
  (let [#^HashMap node-map (:node-map cg)
	final-node         (util/safe-get node-map [*finish-clause* nil])]
    (loop []
      (let [best-rew (util/sref-get (:max-in-reward final-node))]
	(when (> best-rew Double/NEGATIVE_INFINITY)
	  (let [bp (simple-cg-backwards-pass final-node *finish-state* 0 best-rew 0 nil)]
	    (cond (nil? bp)     
		    (recur)
		  (= (first bp) :refine)
		    (do (refine-cg-edge! (:node-map cg) (nth bp 1) (nth bp 2))
			(recur))
		  :else 
		    [(remove #(= % :noop) (map hla-primitive bp)) best-rew])))))))


	

; cg-state-home
; cg-regress-state

; Big question: Can I ever discover a better path to an existing node ???
  ; Certainly, if descriptions are inconsistent.
  ; Can enforce consistency at edge level easily, when we generate refinements.
  ; If descriptions are consistent, then it's still possible, and we may have refined what follows arbitrarily much.
 ; When this happens, just reopen the original edge, iterate recursively.  (no worse than tree or graph).
   ; But how do we know it happens? Should also propagate up the worst value for any state under it ?
   ; NM; an edge is *always* live when incomings exist.  We always reopen, period.  (pess. is only cure.)
 ; Note, path can only be better through *intermediate* nodes.  :>
  
; I know what I update .... but what do I refine ?? I don't refine nodes ???? I refine edges.
; Do I refine incoming or outgoing edges?  Incoming seems best. 
; Do I shift-down incoming or outgoing edges?  Outgoing, it seems.

; Edges can have multiple outlet nodes (per clause)
; Nodes have forward and backward connections to edges,
; edges have only backward connections (at least for now). 
; could have separate edge-clause cache   ...
; Problem: when I refine an edge, I do it for single path.
  ; How can we tell when an edge is "all tapped out"? 
  ; Or, when we shift down, how can we tell if it exists?
  ; Edge stores suffix-set, fine.  

; Refining and shifting-down have same basic consequence

; What do I need to cache ??
; need forward cache (just hla set, mapping to actual edge objects).
 ; When refining, neet to make sure to update costs of duplicates (assuming second sol'n)
 
; When do I shift the source of an edge downwards?  
  ; When you get to a node, and you can't find the state you want, 
    ; and you decrease your value, you clone yourself to all children with > value. 
    ; Edge value goes to infinity when you run out of inputs.
; Edge also handles consistency.

; Only remaining question: when I discover better route to node, what do I reopen?
 ; Everything (except refined)?????  Top-level only?  Either seems OK.
  ; As long as node is worse than its parent, it implicitly inherits its edges.
  ; As soon as edges take on bad cost of parent, they must copy down. 
  ; Edges store last cached incoming cost. 
    ; i.e., I can reopen/create top-level, OR, 
      ; reopen all unrefined actions here and at all ancestors (assuming tree) with <= reward, except
      ; things already copied down.  Easiest seems to be to just start over with top-level
  ; This requires further thought.

; Must I keep track of different incoming clauses separately?  Consistency within, but NOT between.  
 ; need hla, clause, reward

(comment 

(defmethod simple-cg-backwards-pass ::CGNode [node next-state rest-reward target-reward max-gap max-gap-node]
  (util/timeout)
  (when-let [[sub-node best-reward] (cg-state-home node next-state)] ;; Returns nil if bad.
    (util/assert-is (<= (+ best-reward rest-reward) target-reward)) ?
    (when (>= (+ best-reward rest-reward) target-reward)
      (let [[prev-node prev-state hla step-reward gap] (cg-regress-state sub-node next-state)]
	(if-let [rec (simple-cg-backwards-pass prev-node 
		rec (simple-cg-backwards-pass prev-node prev-state prev-reward prev-gap prev-gap-node alg)]
	    (util/assert-is (= prev-s2 prev-state))
					;	(println "SBP gap " (alg-node-name node) gap (class rec))
	    (cond (isa? (:class rec) ::ALGInternalNode) rec
	    rec                                  (conj rec (:hla node))
	    :else (do (invalidate-valuations node)
		      (recur node next-state reward max-gap max-gap-node alg)))))))))
    
(def *ov* )
(defmethod simple-cg-backwards-pass ::ALGMergeNode [node next-state reward max-gap max-gap-node alg]
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
	    (simple-cg-backwards-pass prev-node next-state reward max-gap max-gap-node alg))
	  (do (invalidate-valuations node)
	      (recur node next-state reward max-gap max-gap-node alg))))))

(defn drive-simple-cg-backwards-pass [node]
  (let [alg (:alg node)
	pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(loop []
	  (when-let [[state rew] (valuation-max-reward-state (alg-optimistic-valuation node))]
;	    (println "Driving " state rew)
	    (or (util/sref-set! pass-cache (simple-cg-backwards-pass (:plan node) state rew 0 nil alg))
		(do  (invalidate-valuations node)
		     (recur))))))))

; We don't necessarily need edges either
;(defstruct cg-edge :class :prev-clause :hla :rest-plan :opt-desc :pess-desc :reward



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
;  (println "SBP Root" (alg-node-name node) next-state reward max-gap)
  (util/assert-is (or (Double/isNaN reward) (= reward 0)))
;  (when (or (Double/isNaN reward) (>= reward 0))
    (util/assert-is (= (valuation-state-reward (alg-optimistic-valuation node) next-state) 0))
    (or max-gap-node []))

(defmethod simple-backwards-pass ::ALGActionNode [node next-state reward max-gap max-gap-node alg]
  (util/timeout)
  (let [val-reward (valuation-state-reward (alg-optimistic-valuation node) next-state)]
;  (println "SBP Action" (alg-node-name node) next-state reward val-reward max-gap (:class (alg-optimistic-valuation node)) (:class (alg-optimistic-valuation (util/sref-get (:previous node)))))
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
;	(println "Regress to " regress-pair)
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
    
(def *ov* )
(defmethod simple-backwards-pass ::ALGMergeNode [node next-state reward max-gap max-gap-node alg]
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
	    (simple-backwards-pass prev-node next-state reward max-gap max-gap-node alg))
	  (do (invalidate-valuations node)
	      (recur node next-state reward max-gap max-gap-node alg))))))

(defn drive-simple-backwards-pass [node]
  (let [alg (:alg node)
	pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(loop []
	  (when-let [[state rew] (valuation-max-reward-state (alg-optimistic-valuation node))]
;	    (println "Driving " state rew)
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
      (if (not (isa? (:class bp) ::ALGActionNode))
	(do (println "Warning: trying to refine optimal node")
	    nil)
       (do
;      (def *n* node)
;      (util/assert-is (isa? (:class bp) ::ALGActionNode) "Nothing to refine %s" (print-str (map hla-name bp)))
      (util/print-debug 3 "Refining at " (alg-node-name bp))
      (util/sref-up! search/*ref-counter* inc)
      (let [refs (hla-immediate-refinements (:hla bp) (alg-optimistic-valuation (util/sref-get (:previous bp))))
	    final (replace-node-with-refinements! bp refs)]
	(util/print-debug 3  "Got refinements " (for [r refs] (map hla-name r)))
	[(make-alg-final-node (:alg node)
	  (if (empty? (util/sref-get (:next-map final))) final (:plan node)))]))))))


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



)