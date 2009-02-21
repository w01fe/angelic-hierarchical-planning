(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv]
            [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]))



;; Abstract lookahead trees, with (optional) forward caching and graph stuff.
; Should subsume top_down_forward at some point

; WARNING

; Note: According to node contract, equality should be only on plan-tail and valuations if possible.  This is tree though, so forget that?

;; Nodes
; note that valuations are metadata so they aren't used in comparisons.

; Graph map is metadata on ALT, maps from [state-set rest-plan] --> max-pess-reward.
; MUST contain only active plans, or you can screw yourself?;
; Solution: do it all in node-immediate-refinements??
; OK to prune if strictly dominated by ancestor (assuming consistency)
  ; Or even weakly dominated by non-ancestor refined ?????
   ; YES, if you take duplicate plans into account when defining ancestors.
; If a plan dies a natural death, it's OK to keep its cruft around. 

; SO, three options:
; Don't skip duplicate plans
 ; Prune if strictly dominated by (direct) ancestor,
   ; or weakly dominated by any other plan (refined or not).
; Strengths: as much pruning as possible, 
; Weaknesses: must keep track of ancestors, may multi-generate plans. Replacement policy? Always replace.
;              fails if inconsistent
; Plans can keep track of ancestor set... (use node *names*)
;Go with this for now

; Skip duplicate plans
 ; Prune if strictly domainted by (direct or indirect) ancestor
   ; or weakly dominated by any other plan (refined or not)
; Strengths: as much pruning and skipping as possible
; Weaknesses: must keep track of both direct and indirect ancestors. Replacement policy?

; Skip duplicate plans  (= this version, when used with graph search)
 ; Prune if weakly dominated by any unrefined plan.
; Strengths: simple, just remove refined plans
; Weaknesses: misses out on things like [left right act]

; THIS version also fails to add back cached nodes--bad.

; TODO: add consistency check?


(defstruct abstract-lookahead-tree :cache? :graph? :goal)

(defn first-nonprimitive-alt [node]
  (let [np (:first-np node)]
    (cond (true? np) node
	  np np)))

(derive ::ALTNode :edu.berkeley.ai.search/Node)

(defstruct abstract-lookahead-tree-node  :class :alt :hla :previous :first-np)

(defn make-alt-node [alt hla rest-plan previous-node first-np opt-val pess-val] 
  (let [node   (with-meta  
		(struct abstract-lookahead-tree-node ::ALTNode alt hla previous-node first-np) 
		{:pessimistic-valuation (util/sref pess-val), :optimistic-valuation (util/sref opt-val)
		 :lower-reward-bound (util/sref nil) :upper-reward-bound (util/sref nil) :cache (HashMap.)
		 })]
    (if (not (:graph? alt)) node
      (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	    opt-val    (optimistic-valuation node)
	    opt-states (get-valuation-states opt-val)
	    graph-val  (or (.get graph-map [opt-states rest-plan]) Double/NEGATIVE_INFINITY)]
;	(when (and (>= graph-val (get-valuation-upper-bound opt-val)) (> graph-val Double/NEGATIVE_INFINITY))
;	  (println "pruning!" (search/node-str previous-node) ";" (hla-name hla) ";" (map hla-name rest-plan)))
	(when (> (get-valuation-upper-bound opt-val) graph-val)
	  (let [pess-val    (pessimistic-valuation node)
		pess-states (get-valuation-states pess-val)
		pair        [pess-states rest-plan]]
	    (.put graph-map pair (max (get-valuation-lower-bound pess-val)
				      (or (.get graph-map pair) Double/NEGATIVE_INFINITY))))
	  node)))))
	       


(defn get-alt-node [hla rest-plan previous-node]
  (let [alt (util/safe-get previous-node :alt)]
    (or (and (util/safe-get alt :cache?)
	     (let [#^HashMap cache (util/safe-get ^previous-node :cache)]
;	       (println "GET " (search/node-str previous-node) (hla-name hla) (hla-hierarchical-preconditions hla))
	       (.get cache hla)))
;	       (when-let [x (.get cache hla)]
;		 (println "hit!" (hla-name hla))
;		 x)))
	(let [ret
	      (make-alt-node 
	       alt 
	       hla 
	       rest-plan
	       previous-node 
	       (or (first-nonprimitive-alt previous-node) (when-not (hla-primitive? hla) true))
	       nil nil)]
	  (when (:cache? alt)
	    (let [#^HashMap cache (:cache ^previous-node)]
;	      (println "PUT " (search/node-str previous-node) (hla-name hla) (hla-hierarchical-preconditions hla))
	      (.put cache hla ret)))
	  ret))))

(defn make-alt-root-node [cache? graph? goal initial-valuation initial-plan]
  (make-alt-node 
   (with-meta 
    (struct abstract-lookahead-tree cache? graph? goal)
    (if graph? {:graph-map (HashMap.)} {}))
   :root
   initial-plan
   nil
   nil
   initial-valuation 
   initial-valuation))

(defn make-initial-alt-node 
  ([initial-node] (make-initial-alt-node (hla-default-valuation-type initial-node) initial-node))
  ([valuation-class initial-node]
  (let [env (hla-environment initial-node)]
    (loop [actions (list initial-node)
	   previous (make-alt-root-node 
		     true true; false
		     (envs/get-goal env) 
		     (make-initial-valuation valuation-class env)
		     actions)]
      (if (empty? actions)
        previous
	(recur (rest actions)
	       (get-alt-node (first actions) (rest actions) previous)))))))

(defn alt-node 
  ([initial-hla] (make-initial-alt-node initial-hla))
  ([val-class initial-hla] (make-initial-alt-node val-class initial-hla)))



(defn do-restrict-valuation-alt [x y]
  (restrict-valuation x y))

(defn- pessimistic-valuation [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-pessimistic 
	   (do-restrict-valuation-alt (pessimistic-valuation (:previous node)) 
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-pessimistic-description (:hla node)))))))


(defn optimistic-valuation [node]
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-optimistic 
	   (do-restrict-valuation-alt (optimistic-valuation (:previous node))
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-optimistic-description (:hla node)))))))

(defn node-immediate-refinements [node rest-actions]
  (util/assert-is (not (hla-primitive? (:hla node))))
  (filter identity
    (for [refinement (hla-immediate-refinements (:hla node) (optimistic-valuation (:previous node)))]
      (loop [previous (:previous node),
	     actions (concat refinement rest-actions)]
	(cond (empty? actions)  previous
	      (nil?   previous) nil ; (do (println "pruning!") nil) ;
	      :else
	      (recur 
	       (get-alt-node (first actions) (rest actions) previous)
	       (rest actions)))))))
      

;; Node methods 

(defmethod search/node-environment   ::ALTNode [node] (hla-environment (:hla node)))

(defmethod search/node-state         ::ALTNode [node]
  (if (nil? (:previous (:previous node)))
      (envs/get-initial-state (hla-environment (:hla node)))
    (throw (IllegalArgumentException.))))

(defmethod search/lower-reward-bound ::ALTNode [node] 
  (let [s (:lower-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (get-valuation-lower-bound (do-restrict-valuation-alt (pessimistic-valuation node) (:goal (:alt node))))))))

(defmethod search/upper-reward-bound ::ALTNode [node] 
  (let [s (:upper-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
          (get-valuation-upper-bound (do-restrict-valuation-alt (optimistic-valuation node) (:goal (:alt node))))))))

(defmethod search/reward-so-far ::ALTNode [node] 0)


; Note: what follows assumes that descriptions for primitives are exact.

; TODO: add way to specify which HLA to refine.
(defmethod search/immediate-refinements ::ALTNode [node] 
  (util/timeout)
  (util/sref-set! *ref-counter* (inc (util/sref-get *ref-counter*)))
  (when-let [fnp (first-nonprimitive-alt node)]
    (let [rest-nodes (reverse (take-while #(not (identical? % fnp)) (iterate :previous node)))
	  rest-actions (map :hla rest-nodes)]
      (when (:graph? (:alt node)) ; Remove this plan from cache.
	(let [#^HashMap graph-map (util/safe-get ^(:alt node) :graph-map)]
	  (loop [nodes (cons fnp rest-nodes)
		 actions rest-actions]
	    (when nodes
	      (.remove graph-map [(get-valuation-states (pessimistic-valuation (first nodes))) actions])
	      (recur (rest nodes) (rest actions))))))
      (node-immediate-refinements fnp rest-actions)))) 

(defmethod search/primitive-refinement ::ALTNode [node]
  (when-not (:first-np node)
;    (println (search/node-str node))
    (let [act-seq (remove #(= % :noop)
		   (map (comp hla-primitive :hla) (rest (reverse (util/iterate-while :previous node))))) 
	  upper (get-valuation-upper-bound (optimistic-valuation node))] 
      [act-seq upper])))

(defmethod search/extract-optimal-solution ::ALTNode [node] 
  (when (and (not (:first-np node))
	     (> (search/upper-reward-bound node) Double/NEGATIVE_INFINITY))
    (search/primitive-refinement node)))

(defmethod search/node-str ::ALTNode [node] 
  (util/str-join " " (map (comp hla-name :hla) (rest (reverse (util/iterate-while :previous node))))))



(comment

  (let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (alt-node (get-hierarchy  "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" env))] (time (second (a-star-search node))))

  )