(ns edu.berkeley.ai.angelic.hierarchies.clause-graphs
  (:import [java.util HashMap])
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.angelic.dnf-valuations :as dv]
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
	  (util/sref {}) (util/sref {})))
 ; pre-edges is map from edge to step-cost (avoid expensive hashing)
 ; post-edges is map from hla to edge.

(defn- make-cg-root-node [clause plan-suffix]
  (struct cg-node ::CGRootNode clause plan-suffix (util/sref 0)
	  :root :root :root (util/sref {})))


(defstruct cg-edge :class :source-node :hla :restricted-clause :opt-desc :pess-desc :clause-map :in-reward :suffix-set)

(defn- make-cg-edge [source-node hla]
;  (println (hla-name hla) (hla-optimistic-description hla))
  (let [od (hla-optimistic-description hla)
	restricted-clause (restrict-clause (:clause source-node) (hla-hierarchical-preconditions hla))] 
;    (println "Making edge " (hla-name hla) (:clause source-node) (progress-clause (:clause source-node) od))
    (struct cg-edge ::CGEdge source-node hla restricted-clause
	    od (hla-pessimistic-description hla)
	    (if restricted-clause (progress-clause restricted-clause od) {})  ; TODO: detect subsumption chains.
	    (util/sref Double/NEGATIVE_INFINITY) (util/sref #{}))))


(defstruct clause-graph :class :node-map)
(defn- make-clause-graph [env]
  (struct clause-graph ::ClauseGraph env (envs/get-goal env) (HashMap.)))

(declare add-plan!)
(defn make-clause-graph [initial-node]
  (let [initial-plan [initial-node (hla-finish-hla initial-node)]
	root-clause  (state->clause (envs/get-initial-state (hla-environment initial-node)))
	root-node    (make-cg-root-node root-clause initial-plan)
	node-map     (HashMap. {[root-clause initial-plan]})]
    (add-plan! node-map root-node initial-plan)
    (struct clause-graph ::ClauseGraph node-map))) 
    

;;; Helper functions

(defn- connect-cg-node [#^HashMap node-map edge step-rew clause plan-suffix]
  (let [pair [clause plan-suffix]
	node (or (.get node-map pair)
		 (let [n (make-cg-node clause plan-suffix)]
		   (.put node-map pair n)
		   n))
	pre-edges-ref (:pre-edges node)]
;    (util/assert-is (not (contains? (util/sref-get pre-edges-ref) edge)))
    (util/sref-up! pre-edges-ref assoc edge step-rew)
    node))

(defn- get-cg-node [#^HashMap node-map clause plan-suffix]
  (util/safe-get node-map [clause plan-suffix]))
		 
(defn- get-outgoing-edge [node hla]
  (or (get (util/sref-get (:post-edges node)) hla)
      (let [edge (make-cg-edge node hla)]
	(util/sref-up! (:post-edges node) assoc hla edge)
	edge)))

(defn add-edge! 
  "Add/extend this edge to node, or increase its reward, returning a seq of nodes whose reward increased in the process."
  [node-map node plan-suffix]
  (let [edge (get-outgoing-edge node (first plan-suffix))
	reward (util/sref-get (:max-in-reward node))]
    (util/print-debug 3  "Adding edge " (map hla-name plan-suffix) " in-rew " reward)
    (concat
     (when (> reward (util/sref-get (:in-reward edge)))
       (when (not (empty? (util/sref-get (:suffix-set edge)))) (println "crap!" (map hla-name plan-suffix) (util/sref-get (:in-reward edge)) reward))
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
		    next-node (connect-cg-node node-map edge step-rew clause (next plan-suffix))
		    next-rew  (util/sref-get (:max-in-reward next-node))]
	      :when (> tot-rew next-rew)]
	  (do (util/sref-set! (:max-in-reward next-node) tot-rew)
	      next-node)))))))
	 
(import '[java.util IdentityHashMap])

(defn add-plan! [node-map root-node plan-suffix]
  (loop [nodes [root-node] plan-suffix (seq plan-suffix)]
    (when (and (seq nodes) plan-suffix)
      (recur 
       (let [m (IdentityHashMap.)]
	 (doseq [node nodes,
		 nxt  (add-edge! node-map node plan-suffix)]
	   (.put m nxt true))
	 (seq (.keySet m)))
;       (distinct (doall (mapcat #(add-edge! node-map % plan-suffix) nodes)))
       (next plan-suffix)))))

(defn refine-cg-edge! [node-map edge suffix]
  (util/assert-is (contains? (util/sref-get (:suffix-set edge)) suffix))
  (util/sref-up! (:suffix-set edge) disj suffix)
  (doseq [[clause rew] (:clause-map edge)]
    (let [node      (get-cg-node node-map clause suffix)
	  pre-edges (:pre-edges node)]
;      (util/assert-is (contains? (util/sref-get pre-edges) edge))
      (util/sref-up! pre-edges dissoc edge)))
  (let [source-node (:source-node edge)
	clause      (:clause source-node)
	refs        (hla-immediate-refinements (:hla edge) (dv/make-dnf-valuation ::dv/DNFValuation {clause 0}))]
    (doseq [ref refs]
      (add-plan! node-map source-node (concat ref suffix)))))




(defn- cg-node-best-incoming-edge [node]
  (let [pair
	(util/first-maximal-element second
	  (cons [:dummy Double/NEGATIVE_INFINITY]
		(for [[edge step-rew] (util/sref-get (:pre-edges node))]
		  [edge 
		   (+ (util/sref-get      (:in-reward edge))
		      ;(util/safe-get (:clause-map edge) (:clause node))
		      step-rew)])))]
    (util/sref-set! (:max-in-reward node) (second pair))
    pair))


(comment ; Version without pessimistic, results in always refining first.
(defn cg-edge-regress-state [edge final-clause state]
  "Returns state opt-rew pess-rew"
  (util/print-debug 4 "regress " (:restricted-clause edge) (:clause-map edge) (:class (:opt-desc edge)) final-clause state)
  (let [[final-clause rew]    (util/make-safe (find (:clause-map edge) final-clause))
	[prev-state opt-rew]  (regress-clause-state
			       state
			       (:restricted-clause edge)
			       (:opt-desc edge)
			       [final-clause rew])]
    (util/print-debug 4 "got " prev-state)
    [prev-state opt-rew opt-rew]))
 )


;(comment ; real version
(defn cg-edge-regress-state [edge final-clause state]
  "Returns state opt-rew pess-rew"
  (util/print-debug 4 "regress " (:restricted-clause edge) (:clause-map edge) (:class (:opt-desc edge)) final-clause state)
  (let [[final-clause rew]    (util/make-safe (find (:clause-map edge) final-clause))
	[prev-state opt-rew]  (regress-clause-state
			       state
			       (:restricted-clause edge)
			       (:opt-desc edge)
			       [final-clause rew])
;	(minimal-clause-state (util/safe-get ^final-clause :pre-clause))
	[pess-state pess-rew] (or 
			       (regress-clause-state 
			        state
				(state->clause prev-state)
				(:pess-desc edge)
				nil)
			       [prev-state Double/NEGATIVE_INFINITY])]
    (util/assert-is (>= opt-rew rew))
;    (util/assert-is (= pess-state prev-state))
    (util/print-debug 4 "got " prev-state)
    [prev-state opt-rew pess-rew])) 
 ;)
  

;;; Searching

(defmulti simple-cg-backwards-pass
  "Simple-backwards-pass takes [node next-state reward max-gap max-gap-node],
   and returns either a node to refine, an optimal primitive refinement, or 
   nil (indicating that no plan exists to next-state that achieves reward (>)= reward"
  (fn [node next-state rest-reward target-reward max-gap max-gap-node ] (:class node)))

(defmethod simple-cg-backwards-pass ::CGRootNode [node next-state rest-reward target-reward max-gap max-gap-node]
  (util/assert-is (>= rest-reward target-reward)) ;  ( only = with consistency)
  (util/assert-is (clause-includes-state? (:clause node) next-state))
  (or max-gap-node []))


(defmethod simple-cg-backwards-pass ::CGNode [node next-state rest-reward target-reward max-gap max-gap-node]
  (util/timeout)
;  (util/assert-is (>= (+ (util/sref-get (:max-in-reward node)) rest-reward) target-reward))
  (util/print-debug 3 "Backwards " (:clause node) (map hla-name (:plan-suffix node)) next-state rest-reward)
  (let [[edge best-reward] (cg-node-best-incoming-edge node)]
    (if (> best-reward Double/NEGATIVE_INFINITY)
        (util/print-debug 3 "Got edge " (hla-name (:hla edge)) best-reward)
       (util/print-debug 3  "Got no edges!"))
    (when (>= (+ best-reward rest-reward) target-reward)
      (let [[prev-state opt-rew pess-rew] (cg-edge-regress-state edge (:clause node) next-state)
	    gap                           (- opt-rew pess-rew)
	    prev-node            (:source-node edge)
	    rec                  (simple-cg-backwards-pass prev-node prev-state (+ opt-rew rest-reward)
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
	  (util/print-debug 2 "\n\nDriving " best-rew)
	  (let [bp (simple-cg-backwards-pass final-node *finish-state* 0 best-rew 0 nil)]
	    (cond (nil? bp)     
		    (recur)
		  (= (first bp) :refine)
		    (do (util/print-debug 2 "refining " (:clause (:source-node (nth bp 1))) 
				 (map hla-name (cons (:hla (nth bp 1)) (nth bp 2))))
			(util/sref-up! search/*ref-counter* inc)
		        (refine-cg-edge! (:node-map cg) (nth bp 1) (nth bp 2))
			(recur))
		  :else 
		    [(remove #(= % :noop) (map hla-primitive bp)) best-rew])))))))


(comment 
  (solve-cg (make-clause-graph (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 2 2 [[1 1]] [1 0] true [0 1])))))

)
	

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