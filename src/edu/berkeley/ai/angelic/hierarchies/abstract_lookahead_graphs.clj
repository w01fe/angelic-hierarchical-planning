(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-graphs
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]))



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

(defstruct abstract-lookahead-graph :class :env :goal)
(defn- make-alg [env]
  (struct abstract-lookahead-graph ::AbstractLookaheadGraph env (search/get-goal env)))



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
    (struct alt-action-node ::ALGActionNode hla (ref previous-node) (ref {})))))


(derive ::ALGMergeNode ::ALGInternalNode)
(derive ::ALGRootNode ::ALGMergeNode)
(defstruct alg-merge-node :class :previous-set :next-map)

(defn make-alg-root-node [initial-valuation] 
  (let [n (add-valuation-metadata
	   (struct alt-merge-node ::ALGRootNode (ref #{}) (ref {})))]
    (util/sref-set! (:optimistic-valuation ^n) initial-valuation)
    (util/sref-set! (:pessimistic-valuation ^n) initial-valuation)
    n))


(defn make-alg-merge-node [previous-set]
  (let [n (add-valuation-metadata
	   (struct alt-action-node ::ALGMergeNode (ref (util/to-set previous-node)) (ref {})))]
    (doseq [prev previous-set] (add-child! prev n))
    n))


(derive ::ALGFinalNode ::search/Node)
(defstruct alg-final-node :alg :plan :pass-cache)
(defn make-alg-final-node [alg plan]
  (add-valuation-metadata
   (struct alg-final-node ::ALGFinalNode alg plan (util/sref nil))))



;;; Internal node methods.

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
  (let [new-merge?  (isa? (:class new-node) ::ALGMergeNode)
	post-merge  (get next-map nil)]
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

(defn- make-action-node-seq [prev-node actions]
  (if (empty? actions)
      prev-node
    (if-let [nxt (get-child prev-node (first actions))]
        (recur nxt (rest actions))
      (recur (make-alg-action-node (first actions) prev-node)
	     (next actions)))))


    

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



(declare optimistic-valuation pessimistic-valuation)
(defmulti compute-optimistic-valuation :class)
(defmulti compute-pessimistic-valuation :class)

(defmethod compute-optimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException)))

(defmethod compute-pessimistic-valuation ::ALGRootNode [node]
  (throw (UnsupportedOperationException)))


(defmethod compute-optimistic-valuation ::ALGActionNode [node]
  (progress-optimistic 
   (restrict-valuation (optimistic-valuation (util/sref-get! (:previous node)))
		       (hla-hierarchical-preconditions (:hla node)))
   (hla-optimistic-description (:hla node))))

(defmethod compute-pessimistic-valuation ::ALGActionNode [node]
  (progress-pessimistic 
   (do-restrict-valuation-alt (pessimistic-valuation (util/sref-get! (:previous node)))
			      (hla-hierarchical-preconditions (:hla node)))
   (hla-pessimistic-description (:hla node))))


(defmethod compute-optimistic-valuation ::ALGMergeNode [node]
  (reduce union-valuations (map optimistic-valuation (util/sref-get! (:previous-set node)))))

(defmethod compute-pessimistic-valuation ::ALGMergeNode [node]
  (reduce union-valuations (map pessimistic-valuation (util/sref-get! (:previous-set node)))))


(defmethod compute-optimistic-valuation ::ALGFinalNode [node]
  (restrict-valuation (optimistic-valuation (:plan node)) (:goal (:alg node))))

(defmethod compute-pessimistic-valuation ::ALGFinalNode [node]
  (restrict-valuation (pessimistic-valuation (:plan node)) (:goal (:alg node))))

  

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
  (let [[pre-node post-next-map] (cut-action-node node)
	hla-seqs (remove #(redundant-hla-seq? pre-node post-next-map %) hla-seqs)]
    (if (empty? hla-seqs) pre-node
      (let [final-nodes    (doall (map #(make-action-node-seq pre-node %) hla-seqs))]
	(splice-nexts (or (util/singleton final-nodes) (make-alg-merge-node final-nodes)) post-next-map)))))

  


; helpers for caching progression results

(defn optimistic-valuation [node]
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *op-counter* inc)
	      (compute-optimistic-valuation node))))))

(defn pessimistic-valuation [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *pp-counter* inc)
	      (compute-pessimistic-valuation node))))))


(defn invalidate-valuations [node]
  (util/sref-set! (:optimistic-valuation ^node) nil)
  (util/sref-set! (:pessimistic-valuation ^node) nil)
  nil)


;; Simple backwards-pass

(defmulti simple-backwards-pass
  "Simple-backwards-pass takes [node next-state reward max-gap max-gap-node],
   and returns either a node to refine, an optimal primitive refinement, or 
   nil (indicating that no plan exists to next-state that achieves reward (>)= reward"
  (fn [node next-state reward max-gap max-gap-node] (:class node)))

(defmethod simple-backwards-pass ::ALGRootNode [node next-state reward max-gap max-gap-node]
  (util/assert-is (= reward 0))
  (util/assert-is (= (valuation-state-reward (optimistic-valuation node) next-state) 0))
  max-gap-node)

(defmethod simple-backwards-pass ::ALGActionNode [node next-state reward max-gap max-gap-node]
  (let [val-reward (valuation-state-reward (optimistic-valuation node) next-state)]
    (util/assert-is (<= val-reward reward))
    (when (= val-reward reward)
      (let [prev-node (util/sref-get (:previous node))
	    [prev-state opt-step-reward] (regress-optimistic-state  (optimistic-valuation prev-node)
					                            (optimistic-valuation node) 
								    (hla-optimistic-description (:hla node))
								    next-state)
	    [prev-s2   pess-step-reward] (regress-pessimistic-state (state->valuation prev-state)
								    (pessimistic-valuation node)
								    (hla-pessimistic-description (:hla node))
								    next-state)
	    prev-reward (- reward opt-step-reward)
	    gap         (- opt-step-reward pess-step-reward)
	    [prev-gap prev-gap-node] (if (and (>= gap max-gap) (not (hla-primitive? (:hla node))))
				         [gap node]
				       [max-gap max-gap-node])]
	(util/assert-is (= prev-s2 prev-state))
	(or (simple-backwards-pass prev-node prev-state prev-reward prev-gap prev-gap-node)
	    (do (invalidate-valuations node)
		(recur node next-state reward max-gap max-gap-node)))))))
	
(defmethod simple-backwards-pass ::ALGMergeNode [node next-state reward max-gap max-gap-node]
  (let [val-reward (valuation-state-reward (optimistic-valuation node) next-state)]
    (util/assert-is (<= val-reward reward))
    (when (= val-reward reward)
      (or (when-first [prev-node
		       (filter #(= reward (valuation-state-reward (optimistic-valuation %)))
			       (util/sref-get (:previous-set node)))]
	    (simple-backwards-pass prev-node next-state reward max-gap max-gap-node))
	  (do (invalidate-valuations node)
	      (recur node next-state reward max-gap max-gap-node))))))

(defn drive-simple-backwards-pass [node]
  (let [pass-cache (:pass-cache node)]
    (or (util/sref-get pass-cache)
	(loop []
	  (let [opt-val (optimistic-valuation node)]
	    (when (> (upper-reward-bound opt-val) Double/NEGATIVE_INFINITY)
	      (let [[state rew] (extract-a-best-state opt-val)]
		(or (util/sref-set! pass-cache (simple-backwards-pass (:plan node) state rew 0 nil))
		    (and (invalidate-valuations node)
			 (recur))))))))))

;TODO:  Functions needed: valuation-state-reward, regress-optimistic-state, regress-pessimistic-state, state->valuation, extract-a-best-state.  


;;; Constructing initial ALG nodes

(defn make-initial-alg-node  
  ([initial-node]
     (make-initial-alt-node (hla-default-valuation-type initial-node) initial-node))
  ([valuation-class initial-node]
     (let [initial-plan (list initial-node) 
	   env (hla-environment (first initial-plan)), 
	   alg (make-alg env)]
       (make-alg-final-node alg
         (make-action-node-seq 
	  (make-alg-root-node (state->valuation valuation-class (envs/get-initial-state env)))
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
  (get-valuation-upper-bound (optimistic-valuation node)))

(defmethod search/lower-reward-bound ::ALGFinalNode [node] 
  (get-valuation-lower-bound (pessimistic-valuation node)))

(defmethod search/reward-so-far ::ALGFinalNode [node] 0)

(defmethod search/immediate-refinements ::ALGFinalNode [node] 
  (util/timeout)
  (let [bp (drive-simple-backwards-pass node)]
    (when bp
      (util/assert-is (isa? (:class bp) ::ALGActionNode))
      (util/sref-up! search/*ref-counter* inc)
      (let [final
	    (replace-node-with-refinements! bp
	     (hla-immediate-refinements (:hla bp) (optimistic-valuation (util/sref-get (:previous bp)))))]
	(make-alg-final-node (:alg node)
	  (if (empty? (util/sref-get (:next-map final))) final (:plan node)))))))


(defmethod search/primitive-refinement ::ALGFinalNode [node]
  (let [bp (drive-simple-backwards-pass node)]
    (when (and bp (not (isa? (:class bp) ::ALGActionNode)))
      bp)))

(defmethod search/extract-optimal-solution ::ALGFinalNode [node] 
  (search/primitive-refinement node))



(defmethod search/node-str ::ALGFinalNode [node] 
  "ALG")

(defmethod search/node-first-action ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))

(defmethod search/node-plan-length ::ALGFinalNode [node]
  (throw (UnsupportedOperationException.)))






(comment
(defn get-alt-node [alt hla previous-node] "Returns [node cached?]"
  (let [#^HashMap cache (when (util/safe-get alt :cache?) (util/safe-get ^previous-node :cache))]
    (or (when-let [n (and cache (.get cache hla))] [n true])
	(let [ret (make-alt-node hla previous-node nil nil)]
	  (when cache (.put cache hla ret))
	  [ret false]))))



;; Internal methods

(defn do-restrict-valuation-alt [x y]
  (restrict-valuation x y))

;; Constructing initial nodes






;;; For ICAPS07 algorithm, and perhaps other uses

(defn state->condition [state instance]
  (let [all-atoms (util/to-set (util/safe-get (envs/get-state-space instance) :vars))]
    (envs/make-conjunctive-condition state (util/difference all-atoms state))))

(defn extract-state-seq [plan state-seq]
  (if (nil? (:previous plan))
      state-seq
    (recur (:previous plan)
	   (cons 
	    (extract-a-state 
	     (sub-intersect-valuations 
	      (pessimistic-valuation (:previous plan))
	      (restrict-valuation 
	       (regress-pessimistic
		(state->valuation ::dsv/DNFSimpleValuation (first state-seq))
		(hla-pessimistic-description (:hla plan)))
	       (hla-hierarchical-preconditions (:hla plan)))))						       
	    state-seq))))    

(defn decompose-plan
  "Take a node corresponding to a pessimistically succeeding plan, and return a 
   sequence of fresh nodes corresponding to the subproblem of finding a primitive refinement of that
   particular action."
  [node]
  (util/assert-is (> (search/lower-reward-bound node) Double/NEGATIVE_INFINITY))
  (let [env       (hla-environment (:hla (:plan node)))
	state-seq (extract-state-seq (:plan node) [(extract-a-state 
						    (restrict-valuation 
						     (pessimistic-valuation (:plan node))
						     (envs/get-goal env)))])
	alt       (util/safe-get node :alt)]
  ;  (println "decomposing " (search/node-str node) " on \n" (util/str-join "\n\n" (map #(envs/state-str env %) state-seq)))
    (util/assert-is (= (first state-seq) (envs/get-initial-state env)))
    (util/assert-is (envs/satisfies-condition? (last state-seq) (envs/get-goal env)))
    (map 
     (fn [[s s2] a] 
       (make-initial-alt-node 
	(edu.berkeley.ai.angelic.hierarchies.strips-hierarchies/sub-environment-hla 
	 (:hla a) s (state->condition s2 env))
	(util/safe-get alt :subsumption-info)
	(util/safe-get alt :ref-choice-fn)
	(util/safe-get alt :cache?)
	(util/safe-get alt :graph?)))
     (partition 2 1 state-seq)
     (rest (reverse (util/iterate-while :previous (:plan node)))))))



)