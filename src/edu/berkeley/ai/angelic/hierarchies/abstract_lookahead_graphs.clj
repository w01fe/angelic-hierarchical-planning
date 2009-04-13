(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-graphs
  (:import [java.util HashMap WeakHashMap])
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.graphviz :as graphviz]))


;; Abstract lookahead graphs, which include merge nodes.

; Subsumption is more difficult here, since there's no "rest" of plan to worry about.
; Just ignore it for now, and ignore pessimistic descriptions too.  

; We extract state sequenes going backwards since we need to make consistent choices at or-nodes (merges)
 ; If we didn't ... could certainly end up refining forever (if step reward).
; If total reward ... under certain cycle-free constraints, and other conditions (best non-prim), would eventaully converge.

; So, for suboptimal search, ...
 ;Still need to extract state seq. going backwards.
 ; Analogue of WA*:
  ; Progress WA* function.  
  ; That's hardly feasible? 
  ; Committing is pretty easy. 
  ; When searching, would like slop factor. (change behavior at merge nodes?)

; Like ALT, you should not throw out plans or bad things may happen.

; Would also like improved search algorithm.  

; When you split, you have to be careful, or you could find suboptimal solutions ...
 ; solution; generate new search node every time you increase the cost bound.

; All at once here: 
  ;  Real merging
  ;  Pruning
  ;  Suboptimal search. 


;; TODO: a way to implement extract-a-solution (or refine potentially suboptimal things...)

; TOOD: what do we do when we merge?
  ; We can't merge when we're in the middle of a pass, or we may end up orphaned
  ;  So, we save merges and do them later?  For now, keep track of how we find them.
  ; Merging can potentially increase the value of a node, so we get to deal with all of that.
   ; as long as we keep the *best* plans, we're OK, but we have to be careful about 
    ; when we refine. etc, etc.  

; Cycles cannot be eliminated based solely on optimistic descriptions.  Only pessimistic.  Can only merge into DAG.  

; Handling subsumption:
  ; Each node has a pointer to it's auto-merge node, or nil if none.
  ; Auto-merge keeps a set of nodes it includes. (?)
  ; When we have a hit, if it is or points to an auto-merge, we just check for cycles and join.
  ; If it's not, we check for cycles, then create an auto-merge, then join.
  ; This means there may be multiple unmerged nodes 

; Ideally, also keep track of subsumption relationships we find.  Subsumption may be screwed up by auto-merge, however.  

; Without, just keep track of best pessimistic sub-info.  If we're subsumed, we quit.

; So, maybe we do allow cycles ... just not within merge clusters? 
 ; But then progression becomes a fixed-point calculation.  BLA.
  

; Can there be two possible merge options?  Yes.  Which do we take?  the earliest seems reasonable.  



(defstruct abstract-lookahead-graph :class :env :goal :split-set 
	   :refine-gap? :minimize? :auto-merge? :prune? :smart-search? :consistent-search? :suboptimal-weight)
(defn- make-alg [env split-set refine-gap? minimize? auto-merge? prune? smart-search? consistent-search? suboptimal-weight]
  (with-meta 
   (struct abstract-lookahead-graph ::AbstractLookaheadGraph env (envs/get-goal env) split-set refine-gap? minimize? auto-merge? prune? smart-search? consistent-search? suboptimal-weight)
   {:graph-map (HashMap.)}
   ))
; graph-map maps [opt-states rest-hlas] pairs to
; [canonical-node pess-si-seq]
; [constituent-node-set merge-node]


(defn add-valuation-metadata [node]
  (with-meta node
   {:pessimistic-valuation (util/sref nil), 
    :optimistic-valuation (util/sref nil)}))	     


(declare add-child!)

(derive ::ALGActionNode ::ALGInternalNode)
(defstruct alg-action-node :class :hla :rest-hlas :previous :next-map)
; next-map is a map from hlas to WeakHashMap (used as set of next nodes)..

(defn make-alg-action-node [hla rest-hlas previous-node] 
  (add-child! previous-node
   (add-valuation-metadata
    (struct alg-action-node ::ALGActionNode hla rest-hlas (util/sref previous-node) (util/sref {})))))


(derive ::ALGMergeNode ::ALGInternalNode)
(derive ::ALGRootNode ::ALGMergeNode)
(defstruct alg-merge-node :class :rest-hlas :previous-set :newest-previous :next-map)

(defn make-alg-root-node [initial-plan opt-val pess-val] 
  (let [n (add-valuation-metadata
	   (struct alg-merge-node ::ALGRootNode initial-plan (util/sref #{}) (util/sref nil) (util/sref {})))]
    (util/sref-set! (:optimistic-valuation ^n) opt-val)
    (util/sref-set! (:pessimistic-valuation ^n) pess-val) 
    n))

(derive ::ALGAutoMergeNode ::ALGMergeNode)
(defn make-alg-merge-node [class previous-set rest-hlas]
  (let [n (add-valuation-metadata
	   (struct alg-merge-node class rest-hlas (util/sref (util/to-set previous-set)) (util/sref nil) (util/sref {})))]
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
(defmethod alg-node-name ::ALGAutoMergeNode [node]  "AutoMerge");(str "Merge-" (System/identityHashCode node)))


; Helpers for working with and modifying graph structure

(defn- get-children 
  ([node]
     (apply concat
       (for [k (keys (util/sref-get (util/safe-get node :next-map)))]
	 (get-children node k))))
  ([node key]
     (let [next-map-ref (util/safe-get node :next-map)
	   next-map     (util/sref-get next-map-ref)]
       (when-let [#^WeakHashMap m (get next-map key)]
	 (keys m)))))

(defn- alg-node-key [node]
  [(:hla node) (:rest-hlas node)])

(defn- add-child! [node child]
  (let [next-map-ref (util/safe-get node :next-map)
	next-map     (util/sref-get next-map-ref)
	key          (alg-node-key child)
	old-wrs      (get next-map key)
	#^WeakHashMap wrs 
	               (or old-wrs
			 (let [wrs (WeakHashMap.)]
			   (util/sref-set! next-map-ref (assoc next-map key wrs))
			   wrs))]
    (.put wrs child true)
    child))

(defn- remove-child! [node child]
  (let [#^WeakHashMap m (util/safe-get (util/sref-get (:next-map node)) (alg-node-key child))]
    (assert (.containsKey m child))
    (.remove m child)))


(defmulti add-previous! (fn [node new-prev] (:class node)))

(defmethod add-previous! ::ALGActionNode [node new-prev]
  (let [prev-ref (:previous node)]
    (util/assert-is (nil? (util/sref-get prev-ref)))
    (util/sref-set! prev-ref new-prev)))

(defmethod add-previous! ::ALGMergeNode [node new-prev]
  (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (util/sref-set! (:newest-previous node) new-prev)
    (util/sref-set! prev-ref (conj prev-set new-prev))))


(defmulti remove-previous! (fn [node old-prev] (:class node)))

(defmethod remove-previous! ::ALGActionNode [node old-prev]
  (let [prev-ref (:previous node)]
    (assert (identical? (util/sref-get prev-ref) old-prev))
    (util/sref-set! prev-ref nil)))

(defmethod remove-previous! ::ALGMergeNode [node old-prev]
  (let [prev-ref (:previous-set node)
	prev-set (util/sref-get prev-ref)]
    (assert (contains? prev-set old-prev))
    (util/sref-set! prev-ref (disj prev-set old-prev))))

(defn alg-merge-node-previouses [alg node]
  (if (util/safe-get alg :consistent-search?)
    (let [np (util/sref-get (:newest-previous node))
	  ap (util/sref-get (:previous-set node))]
      (if np (cons np (disj ap np)) ap))
   (util/sref-get (:previous-set node))))

(defn- connect! [node child]
  (add-previous! child node)
  (add-child! node child))

(defn- disconnect! [node child]
  (remove-previous! child node)
  (remove-child! node child))


(defn- cut-action-node [node]
  (util/assert-is (isa? (:class node) ::ALGActionNode))
  (doseq [nxt (get-children node)] 
    (remove-previous! nxt node))
  (let [ret [(util/sref-get (:previous node)) (util/sref-get (:next-map node))]]
    (util/sref-set! (:next-map node) {})
    (disconnect! (util/sref-get (:previous node)) node)
    ret))


(defn- splice-nexts [new-node next-map minimize?]
;  (println "SN" (:class new-node) (count (alg-node-parents new-node)) (count (alg-node-children new-node)))
  (condp = minimize?
         false
	   (do (assert (empty? (util/sref-get (:next-map new-node))))
	       (util/sref-set! (:next-map new-node) next-map)
	       (doseq [child (get-children new-node)]
		 (add-previous! child new-node)))
	 :forward
	   (doseq [#^WeakHashMap child-wrs  (vals next-map)
		   child                    (keys child-wrs)]
	     (connect! new-node child))
	 :full
	   (doseq [[k #^WeakHashMap child-wrs] next-map]
	     (let [new-children (keys child-wrs)
		   old-children (get-children new-node k)]
	       (util/assert-is (<= (count old-children) 1))
	       (util/assert-is (<= (count new-children) 1))
	       (if (empty? old-children)
		   (doseq [new-child new-children]
		     (connect! new-node new-child))
		 (when (not (empty? new-children)) (println "Splice")
		   (doseq [new-child new-children]
		     (doseq [nxt (get-children new-child)]
		       (remove-previous! nxt new-child))
		     (splice-nexts (first old-children) (util/sref-get (:next-map new-child)) minimize?)))))))
  new-node)


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
(defn- make-action-node-seq [prev-node actions rest-actions track-actions? minimize?]
;  (println (map hla-name actions))
  (if (empty? actions) 
      prev-node
    (recur (or (and minimize? 
		    (when-let [n (first (get-children prev-node (first actions)))]
		      ;(println "reuse") 
		      n)) ;; TODO: wrong with multiple children?
	       (make-alg-action-node (first actions) (when track-actions? (concat (next actions) rest-actions)) prev-node))
	   (next actions)
	   rest-actions track-actions? minimize?)))

(comment
  (util/assert-is (not (empty? actions)))
  (if-let [singleton (util/singleton actions)]
      (make-alg-action-node singleton prev-node)
    (recur (or (first (get-children prev-node (first actions))) ;; TODO: wrong with multiple children?
	       (make-alg-action-node (first actions) prev-node))
	   (next actions))))

      


;;; Computing valuations, etc.

(declare alg-optimistic-valuation alg-pessimistic-valuation)
(defmulti compute-alg-optimistic-valuation (fn [alg node] (:class node)))
(defmulti compute-alg-pessimistic-valuation (fn [alg node] (:class node)))

(defmethod compute-alg-optimistic-valuation ::ALGRootNode [alg node]
  (throw (UnsupportedOperationException.)))

(defmethod compute-alg-pessimistic-valuation ::ALGRootNode [alg node]
  (throw (UnsupportedOperationException.)))


(defmethod compute-alg-optimistic-valuation ::ALGActionNode opt-action [alg node]
;  (println "Progress action " (hla-name (:hla node)))
  (let [previous (util/sref-get (:previous node))]
    (if (nil? previous)
        *pessimal-valuation*
      (progress-valuation 
       (restrict-valuation (alg-optimistic-valuation alg previous)
			   (hla-hierarchical-preconditions (:hla node)))
       (hla-optimistic-description (:hla node))))))

(defmethod compute-alg-pessimistic-valuation ::ALGActionNode pess-action [alg node]
  (let [previous (util/sref-get (:previous node))]
    (if (nil? previous)
        *pessimal-valuation*
      (progress-valuation 
       (restrict-valuation (alg-pessimistic-valuation alg previous)
			   (hla-hierarchical-preconditions (:hla node)))
       (hla-pessimistic-description (:hla node))))))


(defmethod compute-alg-optimistic-valuation ::ALGMergeNode opt-merge [alg node]
;  (println "Progress merge ")
  (let [vals (for [e (alg-merge-node-previouses alg node)
		   :let [val (alg-optimistic-valuation alg e)]
		   :when (if (empty-valuation? val)
			     (do (disconnect! e node) nil)
			   true)]
	       (add-clause-metadata val {:source-node e}))]
    (if (empty? vals) *pessimal-valuation*
      (reduce union-valuations vals))))
;	      (for [n pruned-set]
;		(add-clause-metadata (alg-optimistic-valuation alg n) {:source-node n}))))))
	      ;(map alg-optimistic-valuation pruned-set)))))

(defmethod compute-alg-pessimistic-valuation ::ALGMergeNode pess-merge [alg node]
  (let [previous-set (util/sref-get (:previous-set node))]
    (if (empty? previous-set) *pessimal-valuation*
      (reduce union-valuations (map #(alg-pessimistic-valuation alg %) previous-set)))))


(defmethod compute-alg-optimistic-valuation ::ALGFinalNode opt-final [alg node]
  (restrict-valuation (alg-optimistic-valuation alg (:plan node)) (:goal (:alg node))))

(defmethod compute-alg-pessimistic-valuation ::ALGFinalNode pess-final [alg node]
  (restrict-valuation (alg-pessimistic-valuation alg (:plan node)) (:goal (:alg node))))

(declare invalidate-valuations)
(defn handle-graph [alg node]
  (let [#^HashMap graph-map (util/safe-get ^alg :graph-map)
	opt-val             (util/sref-get (:optimistic-valuation ^node))
	[opt-states _]      (get-valuation-states opt-val {})
	rest-hlas           (util/safe-get node :rest-hlas)
	key-pair            [opt-states rest-hlas]]
    (if-let [[#^WeakHashMap s m-ref] (.get graph-map key-pair)]
        (when (not (.containsKey s node))
	  (println "\n\nMerge\n\n" (:class node) (when (:hla node) (hla-name (:hla node))) (map hla-name (:rest-hlas node)) (if (util/sref-get m-ref) "merged" "new") (count s) (map :class (keys s)))
	  (if (and (nil? (util/sref-get m-ref))
		   (isa? (:class (first (keys s))) ::ALGActionNode)
		   (= nil (util/sref-get (:previous (first (keys s))))))
	    (do (println "dead node")
		(.clear s)
		(.put s node true))
	    (do
	  (when (nil? (util/sref-get m-ref))
	    (util/assert-is (= (.size s) 1))
	    (let [other-node (first (keys s))
		  other-next-ref (:next-map other-node)
		  other-next-map (util/sref-get other-next-ref)]
	      (doseq [nxt (get-children other-node)] 
		(remove-previous! nxt other-node))
	      (util/sref-set! other-next-ref {})
	      (let [new-merge (make-alg-merge-node ::ALGAutoMergeNode [other-node] rest-hlas)]
		(util/sref-set! (:next-map new-merge) other-next-map)
		(doseq [nxt (get-children new-merge)] 
		  (add-previous! nxt new-merge))
		(.put s new-merge true)
		(util/sref-set! m-ref new-merge))))
	  (.put s node true)
	  (let [merge (util/sref-get m-ref)
		next-map-ref (:next-map node)
		next-map     (util/sref-get next-map-ref)]
	    (invalidate-valuations merge)
	    (doseq [nxt (get-children node)] 
	      (remove-previous! nxt node))
	    (util/sref-set! next-map-ref {})
	    (connect! node merge)
	    (splice-nexts merge next-map (or (util/safe-get alg :minimize?) :forward)))))) ;; TODO ???
      (.put graph-map key-pair [(WeakHashMap. {node true}) (util/sref nil)])))) 
;				(util/sref (when (isa? (:class node) ::ALGMergeNode) node))]))))


(defn alg-optimistic-valuation 
;  ([alg node] (alg-optimistic-valuation alg node #{}))
  ([alg node]
;     (if (contains? post-set node)
;         (do (println "Killing cycle!") *pessimal-valuation*)
       (let [s (:optimistic-valuation ^node)]
;	 (when (nil? s) (clojure.inspector/inspect-tree node))
	 (or (util/sref-get s)
	     (do
	       (util/sref-up! *op-counter* inc)
	       (util/sref-set! s (compute-alg-optimistic-valuation alg node)) ; (conj post-set node)))
	       (when (and (:auto-merge? alg) (not (isa? (:class node) ::ALGFinalNode)))
		 (handle-graph alg node))
	       (util/sref-get s))))))

(defn alg-pessimistic-valuation [alg node]
;  *pessimal-valuation*) ; TODO
;(comment
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *pp-counter* inc)
	      (compute-alg-pessimistic-valuation alg node))))))


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
;  (println "SBP Root" );(alg-node-name node) next-state reward max-gap)
  (util/assert-is (or (Double/isNaN reward) (= reward 0)))
;  (when (or (Double/isNaN reward) (>= reward 0))
    (util/assert-is (= (valuation-state-reward (alg-optimistic-valuation alg node) next-state) 0))
    (or max-gap-node []))

(defmethod simple-backwards-pass ::ALGActionNode sbp-action [node next-state next-clause reward max-gap max-gap-node alg]
 ; (println "SBP Action" (map hla-name (cons (:hla node) (:rest-hlas node))));(alg-node-name node) next-state reward max-gap)
  (util/timeout)
 ;   (when next-clause (util/assert-is (clause-includes-state? next-clause next-state)))
  (let [prev-node (util/sref-get (:previous node))
	prev-val (alg-optimistic-valuation alg prev-node)]
    (let [[prev-state step-reward pre-reward prev-clause]
	  (or (regress-state-hinted next-state prev-val (hla-optimistic-description (:hla node)) 
				    (alg-optimistic-valuation alg node) next-clause)
	      [:dummy Double/NEGATIVE_INFINITY Double/NEGATIVE_INFINITY])]
      (if (>= (+ pre-reward step-reward) reward)
	  (let [refine-gap? (util/safe-get alg :refine-gap?)
		[next-gap next-gap-node] 
                  (if refine-gap?
		      (let [[_ pess-step-reward] 
			      (or (regress-clause-state
				   next-state
				   (state->clause prev-state)
				   (hla-pessimistic-description (:hla node))
				   nil)
				  [prev-state Double/NEGATIVE_INFINITY])
			    gap (- step-reward pess-step-reward)]
			(if (and (>= gap max-gap) (not (hla-primitive? (:hla node))))
			    [gap node]
			  [max-gap max-gap-node]))
		    (if (not (hla-primitive? (:hla node))) 
		        [0 node]
		      [0 max-gap-node]))
		rec (simple-backwards-pass prev-node prev-state prev-clause pre-reward next-gap next-gap-node alg)]
	    (cond (isa? (:class rec) ::ALGInternalNode)
		    (if (not (and (util/safe-get alg :smart-search?) 
				  (identical? rec node)
				  (not (empty? (get-children node))))) 
		        rec
		      (let [minimize? (util/safe-get alg :minimize?)
			    auto-merge? (util/safe-get alg :auto-merge?)
			    merge-full? (= auto-merge? true)
			    hla         (:hla rec)
			    rest-hlas (util/safe-get rec :rest-hlas)
			    refs   (hla-immediate-refinements hla (alg-optimistic-valuation alg (util/sref-get (:previous node))))
			    [pre-node post-next-map] (cut-action-node node)
			    final-nodes (doall (map #(make-action-node-seq pre-node % rest-hlas merge-full? minimize?) refs))]
			(util/print-debug 3 "Internally Refining at " (alg-node-name node) ";\nGot refinements " (for [r refs] (map hla-name r)))
			(util/sref-up! search/*ref-counter* inc)
			(let [spliced (splice-nexts (or (util/singleton final-nodes) 
							(make-alg-merge-node ::ALGMergeNode final-nodes rest-hlas)) 
							post-next-map minimize?)]
			  (simple-backwards-pass spliced next-state nil reward max-gap max-gap-node alg))))
		  rec   
		    (conj rec (:hla node))
		  :else                            
		    (recur node next-state nil reward max-gap max-gap-node alg)))
	(invalidate-valuations node)))))


   
(defmethod simple-backwards-pass ::ALGMergeNode sbp-merge [node next-state next-clause reward max-gap max-gap-node alg]
 ; (println "SBP Merge" (map hla-name (:rest-hlas node)));(alg-node-name node) next-state reward max-gap)
 ; (when next-clause (util/assert-is (clause-includes-state? next-clause next-state)))
  (if next-clause
      (or 
        (when-let [prev-node (get ^next-clause :source-node)]
	  (when (and (contains? (util/sref-get (:previous-set node)) prev-node)
		     (or (not (= :strict (util/safe-get alg :consistent-search?)))
			 (let [np (util/sref-get (:newest-previous node))]
;			   (util/assert-is (or (nil? np) (identical? np prev-node)))
			   (or (nil? np) (identical? np prev-node)))))
	    (when-let [[clause val-reward] (valuation-clause-reward (alg-optimistic-valuation alg prev-node) next-clause)]
	      (when (>= val-reward reward); (println "GO")
	;	(print ",")
		(simple-backwards-pass prev-node next-state clause reward max-gap max-gap-node alg)))))
	(recur node next-state nil reward max-gap max-gap-node alg))
    (loop [good-preds
	       (seq (filter identity
		     (for [prev-node (alg-merge-node-previouses alg node)]
		       (let [prev-val (alg-optimistic-valuation alg prev-node)]
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
		      
     
(defn get-max-reward-state-and-clause [v]
  (if (isa? (:class v) :edu.berkeley.ai.angelic/PropositionalValuation)
      (when-let [[clause rew] (valuation-max-reward-clause v)]
	[(minimal-clause-state clause) rew clause])
    (valuation-max-reward-state v)))

(defn drive-simple-backwards-pass [node]
 ; (println "\n\n\n DRIVE")
  (let [alg (:alg node)
	pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(util/sref-set! pass-cache
	  (or
	    (when-let [[state rew clause] (get-max-reward-state-and-clause (alg-optimistic-valuation alg node))]
	      (or (simple-backwards-pass (:plan node) state clause rew 0 nil alg)
		  (do (invalidate-valuations node) nil)))
	    :fail)))))



;;; Constructing initial ALG nodes

(defn make-initial-alg-node  
  "Make an initial ALG node.  
     split-set is a set of HLA names to split on (rather than merge, the default).
     refine-gap? controls whether the opt-pess gap is used to pick what to refine, or if the first HLA is refined.
     minimize? causes the ALG to attempt to share prefixes as much as possible, or not at all.
     auto-merge? causes the graph to merge nodes which have, or have ever had, the same optimistic sets."
  ([initial-node]
     (make-initial-alg-node initial-node #{} false true true))
  ([initial-node split-set refine-gap? minimize? auto-merge? prune? smart-search? consistent-search? suboptimal-weight]
     (make-initial-alg-node 
      (hla-default-optimistic-valuation-type initial-node) 
      (hla-default-pessimistic-valuation-type initial-node)
      initial-node split-set  refine-gap? minimize? auto-merge?  prune? smart-search? consistent-search? suboptimal-weight))
  ([opt-valuation-class pess-valuation-class initial-node split-set refine-gap? minimize? auto-merge?  prune? smart-search? consistent-search? suboptimal-weight]
     (util/assert-is (contains? '#{true false :sloppy} auto-merge?))
     (util/assert-is (contains? '#{false :forward :full} minimize?))
     (util/assert-is (contains? '#{false :local :global} prune?))
     (util/assert-is (contains? '#{false :lazy :strict} consistent-search?))
     (let [initial-plan (list initial-node) 
	   env (hla-environment (first initial-plan)), 
	   alg (make-alg env split-set refine-gap? minimize? auto-merge? prune? smart-search? consistent-search? suboptimal-weight)
	   init-opt (state->valuation opt-valuation-class (envs/get-initial-state env))]
       (make-alg-final-node alg
         (make-action-node-seq 
	  (make-alg-root-node
	   initial-plan
	   init-opt 
	   (state->valuation pess-valuation-class (envs/get-initial-state env)))
	  initial-plan
	  nil (= auto-merge? true) false)))))

(defn alg-node [& args] (apply make-initial-alg-node args))





;;; Node methods 

(defmethod search/reroot-at-node ::ALGFinalNode [node & args]
  (throw (UnsupportedOperationException.)))

(defmethod search/node-environment   ::ALGFinalNode [node] 
  (util/safe-get-in node [:alg :env]))

(defmethod search/node-state         ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod search/upper-reward-bound ::ALGFinalNode [node] 
  (valuation-max-reward (alg-optimistic-valuation (:alg node) node)))

(defmethod search/lower-reward-bound ::ALGFinalNode [node] 
  (valuation-max-reward (alg-pessimistic-valuation (:alg node) node)))

(defmethod search/reward-so-far ::ALGFinalNode [node] 0)

(defmethod search/immediate-refinements ::ALGFinalNode [node] 
  (util/timeout)
;  (println "IR " (System/identityHashCode node))
  (let [bp (drive-simple-backwards-pass node)
	alg (:alg node)]
    (util/assert-is (identity bp))
    (cond (= bp :fail)
 	    (when (> (valuation-max-reward (alg-optimistic-valuation alg node)) Double/NEGATIVE_INFINITY)
	      [(make-alg-final-node alg (:plan node))])
	  (not (isa? (:class bp) ::ALGActionNode))
	    (do (println "Warning: trying to refine optimal node")
		nil)
	  :else 
	    (let [minimize? (util/safe-get alg :minimize?)
		  auto-merge? (util/safe-get alg :auto-merge?)
		  merge-full? (= auto-merge? true)
		  hla       (:hla bp)
		  rest-hlas (util/safe-get bp :rest-hlas)
		  split? (contains? (util/safe-get-in node [:alg :split-set]) (first (hla-name hla)))
		  final? (empty? (get-children bp))
		  refs   (hla-immediate-refinements (:hla bp) (alg-optimistic-valuation alg (util/sref-get (:previous bp))))
		  [pre-node post-next-map] (cut-action-node bp)
		  final-nodes (doall (map #(make-action-node-seq pre-node % rest-hlas merge-full? minimize?) refs))]
	      (when split? (util/assert-is (identity final?)))
	      (util/print-debug 3 "Refining at " (alg-node-name bp) ";\nGot refinements " (for [r refs] (map hla-name r)))
	      (util/sref-up! search/*ref-counter* inc)
	      (if split? 
		  (map #(make-alg-final-node alg %) final-nodes)
		(when (not (and final? (empty? final-nodes)))
		  (let [spliced (splice-nexts (or (util/singleton final-nodes) 
						  (make-alg-merge-node ::ALGMergeNode final-nodes rest-hlas)) 
					      post-next-map minimize?)]
		    [(make-alg-final-node alg (if final? spliced (:plan node)))])))))))


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
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation (:alg node) n))
	    (valuation-max-reward (alg-optimistic-valuation (:alg node) n))])
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
   (fn [n] [(valuation-max-reward (alg-pessimistic-valuation (:alg node) n))
	    (valuation-max-reward (alg-optimistic-valuation (:alg node) n))])
   (fn [n] 
     (for [nxt (get-children n)]
       [(alg-node-name nxt)
	nxt])))
  (util/sh "open" "-a" "Skim" "/tmp/alg.pdf"))

  
(comment 

(do (reset-ref-counter) [(time (second (a-star-search (alg-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 20 20 [[3 7] [12 18] [16 2]] [19 0] true [0 19]))) '#{act go} false false true)))) (sref-get *ref-counter*)])

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