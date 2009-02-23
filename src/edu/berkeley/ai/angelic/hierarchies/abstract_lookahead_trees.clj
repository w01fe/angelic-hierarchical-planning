(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv]
            [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]))



;; Abstract lookahead trees, with (optional) forward caching and graph stuff.
; Should subsume top_down_forward at some point

; WARNING: plan-Graph search will not work here!  Cannot eliminate duplicate plans due to
; iteraction with state-graph..

; WARNING: can't reuse this (when graph true) or will end up with bad results... possible
 ; failure, or suboptimal plans...

;; Nodes
; note that valuations are metadata so they aren't used in comparisons.

; Graph map is metadata on ALT, maps from [state-set rest-plan] --> max-pess-reward.
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
; This way, can't share nodes at aLL!>!>!> Idea: just store ancestors at final node of plan.
; Just 

; Skip duplicate plans
 ; Prune if strictly domainted by (direct or indirect) ancestor
   ; or weakly dominated by any other plan (refined or not)
; Strengths: as much pruning and skipping as possible
; Weaknesses: must keep track of both direct and indirect ancestors. Replacement policy?

; Skip duplicate plans  (= old version 2f3753c, when used with graph search)
 ; Prune if weakly dominated by any unrefined plan.
; Strengths: simple, just remove refined plans
; Weaknesses: misses out on things like [left right act]

; TODO: add consistency check?


(defstruct abstract-lookahead-tree :cache? :graph? :goal)

(defn first-nonprimitive-alt [node]
  (let [np (:first-np node)]
    (cond (true? np) node
	  np np)))

(derive ::ALTPlanNode :edu.berkeley.ai.search/Node)
(defstruct alt-plan-node :class :name :plan :ancestor-set)
(defn make-alt-plan-node [name plan ancestor-set]
  (struct alt-plan-node ::ALTPlanNode name plan ancestor-set))

;(derive ::ALTNode :edu.berkeley.ai.search/Node)

(defstruct alt-action-node :alt :hla :previous :first-np)

(def *dummy-pair-alt* [Double/NEGATIVE_INFINITY (gensym)])

(declare optimistic-valuation pessimistic-valuation)

;; TODO: do fun stuff with ancestor set
(defn make-alt-node [alt hla rest-plan previous-node first-np name ancestor-set opt-val pess-val] 
  (let [node   (with-meta  
		(struct alt-action-node alt hla previous-node first-np) 
		{:pessimistic-valuation (util/sref pess-val), :optimistic-valuation (util/sref opt-val)
		 :lower-reward-bound (util/sref nil) :upper-reward-bound (util/sref nil) :cache (HashMap.)
		 })]
    (if (not (:graph? alt)) node
      (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	    opt-val    (optimistic-valuation node)
	    opt-states (get-valuation-states opt-val)
	    opt-rew    (get-valuation-upper-bound opt-val)
	    [graph-rew graph-node]  (or (.get graph-map [opt-states rest-plan]) *dummy-pair-alt*)]
;	(when (not (or (> opt-rew graph-rew) (and (= opt-rew graph-rew) (contains? ancestor-set graph-node))))
;	  (println "pruning!" name ancestor-set graph-node graph-rew opt-rew (contains? ancestor-set graph-node)))
;	  (println "pruning!" graph-node ancestor-set (when previous-node (search/node-str previous-node)) ";" (hla-name hla) ";" (map hla-name rest-plan)))
	(when (or (> opt-rew graph-rew) (and (= opt-rew graph-rew) (contains? ancestor-set graph-node)))
	  (let [pess-val    (pessimistic-valuation node)
		pess-states (get-valuation-states pess-val)
		pess-rew    (get-valuation-lower-bound pess-val)
		pair        [pess-states rest-plan]
		[graph-rew graph-node] (or (.get graph-map pair) *dummy-pair-alt*)]
	    (when (>= pess-rew graph-rew)
	      (.put graph-map pair [pess-rew name])))
;	    (.put graph-map pair (max (get-valuation-lower-bound pess-val)
;				      (or (.get graph-map pair) Double/NEGATIVE_INFINITY))))
	  node)))))
	       


(defn get-alt-node [hla rest-plan previous-node name ancestor-set]
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
	       name ancestor-set
	       nil nil)]
	  (when (:cache? alt)
	    (let [#^HashMap cache (:cache ^previous-node)]
;	      (println "PUT " (search/node-str previous-node) (hla-name hla) (hla-hierarchical-preconditions hla))
	      (.put cache hla ret)))
	  ret))))

(defn make-alt-root-node [cache? graph? goal initial-valuation initial-plan name]
  (make-alt-node 
   (with-meta 
    (struct abstract-lookahead-tree cache? graph? goal)
    (if graph? {:graph-map (HashMap.)} {}))
   :root
   initial-plan
   nil
   nil
   name
   #{}
   initial-valuation 
   initial-valuation))

(defn make-initial-alt-node 
  ([initial-node] (make-initial-alt-node (hla-default-valuation-type initial-node) initial-node))
  ([initial-node cache? graph?] (make-initial-alt-node (hla-default-valuation-type initial-node) initial-node cache? graph?))
  ([valuation-class initial-node] (make-initial-alt-node valuation-class initial-node true true))
  ([valuation-class initial-node cache? graph?]
  (let [env (hla-environment initial-node), name (gensym)]
    (loop [actions (list initial-node)
	   previous (make-alt-root-node 
		     cache? graph?
		     (envs/get-goal env) 
		     (make-initial-valuation valuation-class env)
		     actions
		     name)]
      (if (empty? actions)
          (make-alt-plan-node name previous #{})
	(recur (rest actions)
	       (get-alt-node (first actions) (rest actions) previous name #{})))))))

(defn alt-node [& args] (apply make-initial-alt-node args))
;  ([initial-hla] (make-initial-alt-node initial-hla))
;  ([val-class initial-hla] (make-initial-alt-node val-class initial-hla)))



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


(defn- optimistic-valuation [node]
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-optimistic 
	   (do-restrict-valuation-alt (optimistic-valuation (:previous node))
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-optimistic-description (:hla node)))))))

(defn- node-immediate-refinements [node rest-actions name ancestors]
  (util/assert-is (not (hla-primitive? (:hla node))))
  (filter identity
    (for [refinement (hla-immediate-refinements (:hla node) (optimistic-valuation (:previous node)))]
      (loop [previous (:previous node),
	     actions (concat refinement rest-actions)]
	(cond (empty? actions)  previous
	      (nil?   previous) nil ; (do (println "pruning!") nil) ;
	      :else
	      (recur 
	       (get-alt-node (first actions) (rest actions) previous name ancestors)
	       (rest actions)))))))
      

;; Node methods 

(defmethod search/node-environment   ::ALTPlanNode [node] (hla-environment (:hla (:plan node))))

(defmethod search/node-state         ::ALTPlanNode [node]
  (if (nil? (:previous (:previous (:plan node))))
      (envs/get-initial-state (hla-environment (:hla (:plan node))))
    (throw (IllegalArgumentException.))))

(defmethod search/lower-reward-bound ::ALTPlanNode [node] 
  (let [node (:plan node)
	s (:lower-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (get-valuation-lower-bound (do-restrict-valuation-alt (pessimistic-valuation node) (:goal (:alt node))))))))

(defmethod search/upper-reward-bound ::ALTPlanNode [node] 
  (let [node (:plan node)
	s (:upper-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
          (get-valuation-upper-bound (do-restrict-valuation-alt (optimistic-valuation node) (:goal (:alt node))))))))

(defmethod search/reward-so-far ::ALTPlanNode [node] 0)


; Note: what follows assumes that descriptions for primitives are exact.

; TODO: add way to specify which HLA to refine.
(defmethod search/immediate-refinements ::ALTPlanNode [node] 
  (util/timeout)
  (util/sref-set! *ref-counter* (inc (util/sref-get *ref-counter*)))
  (let [plan (:plan node)]
    (when-let [fnp (first-nonprimitive-alt plan)]
      (let [rest-nodes (reverse (take-while #(not (identical? % fnp)) (iterate :previous plan)))
	    rest-actions (map :hla rest-nodes)
	    name (gensym)
	    ancestors (conj (util/safe-get node :ancestor-set) (util/safe-get node :name))]
	(map #(make-alt-plan-node name % ancestors)
	     (node-immediate-refinements fnp rest-actions name ancestors)))))) 

(defmethod search/primitive-refinement ::ALTPlanNode [node]
  (let [node (:plan node)]
    (when-not (:first-np node)
;    (println (search/node-str node))
    (let [act-seq (remove #(= % :noop)
		   (map (comp hla-primitive :hla) (rest (reverse (util/iterate-while :previous node))))) 
	  upper (get-valuation-upper-bound (optimistic-valuation node))] 
      [act-seq upper]))))

(defmethod search/extract-optimal-solution ::ALTPlanNode [node] 
  (when (and (not (:first-np (:plan node)))
	     (> (search/upper-reward-bound node) Double/NEGATIVE_INFINITY))
    (search/primitive-refinement node)))

(defmethod search/node-str ::ALTPlanNode [node] 
  (util/str-join " " (map (comp hla-name :hla) (rest (reverse (util/iterate-while :previous (:plan node)))))))



(comment

  (let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (alt-node (get-hierarchy  "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" env))] (time (second (a-star-search node))))

  )






;; Tests and other miscellanea



(defn- get-and-check-sol [sol initial-hla]
  (doseq [cache? [true false]
	  graph? [true false]]
    (util/is (contains? sol 
      (map :name
         (first
	  (envs/check-solution (hla-environment initial-hla)
	    (edu.berkeley.ai.search.algorithms.textbook/a-star-search
	    (alt-node initial-hla cache? graph?)))))))))


(require '[edu.berkeley.ai.domains.nav-switch :as nav-switch])
(require '[edu.berkeley.ai.domains.strips :as strips])
(require '[edu.berkeley.ai.domains.warehouse :as warehouse])
(require '[edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as strips-hierarchies])
(require '[edu.berkeley.ai.search.algorithms.textbook :as textbook])


(def *flat-ns* (nav-switch/make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *flat-ns-sol* #{['left 'flip 'down]})

(def *strips-ns* (nav-switch/make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *strips-ns-sol* #{'[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]})

(def *flat-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 1))))))
(def *strips-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) 1))))))

(def *simplifiers* [identity 
		     strips/constant-predicate-simplify
		     (comp strips/flatten-strips-instance strips/constant-predicate-simplify)])

(util/deftest alt-nav-switch
   (util/testing "flat hierarchy, non-strips"
     (get-and-check-sol *flat-ns-sol* (get-flat-hierarchy *flat-ns*))
     (get-and-check-sol *flat-ns-sol* (get-flat-hierarchy *flat-ns* *flat-ns-heur*)))
   (util/testing "flat hierarchy, strips"
     (get-and-check-sol *strips-ns-sol* (get-flat-hierarchy *strips-ns* *strips-ns-heur*))
     (doseq [simplifier *simplifiers*]
       (get-and-check-sol *strips-ns-sol* (get-flat-hierarchy (simplifier *strips-ns*)))))
   (util/testing "flat-strips hierarchy"
     (get-and-check-sol *strips-ns-sol* (strips-hierarchies/get-flat-strips-hierarchy *strips-ns* *strips-ns-heur*))
     (doseq [simplifier (butlast *simplifiers*)]
       (get-and-check-sol *strips-ns-sol* (strips-hierarchies/get-flat-strips-hierarchy (simplifier *strips-ns*)))))
   (util/testing "Ordinary strips hierarchy"
     (doseq [simplifier (butlast *simplifiers*)]
       (get-and-check-sol *strips-ns-sol* (get-hierarchy nav-switch/*nav-switch-hierarchy* (simplifier *strips-ns*))))))		

(def *strips-wh* (warehouse/make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))
(def *strips-wh-sols* 
  #{'((get-l a table0 x0 x1 y1) (left x1 x0 y1) (turn-r x0 y1) (put-r a table1 x1 x0 y0 y1))
	 '((get-l a table0 x0 x1 y1) (turn-r x1 y1) (left x1 x0 y1) (put-r a table1 x1 x0 y0 y1))}) 			      






(util/deftest alt-down-warehouse
 (util/testing "flat-strips hierarchy"
   (doseq [simplifier (butlast *simplifiers*)
	   maker [strips-hierarchies/get-flat-strips-hierarchy 
		  #(get-hierarchy warehouse/*warehouse-hierarchy-unguided* %)]]
     (get-and-check-sol *strips-wh-sols* (maker (simplifier *strips-wh*))))))

      


; Misc crap below, more or less out of date.

(comment 
  (let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])] 
    (map :name (first (a-star-search 
    (make-initial-alt-node 
     :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation
     (instantiate-hierarchy
	    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env)) 
    ))))



(let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])
	    node
    (make-initial-alt-node 
     :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation
     (instantiate-hierarchy
	    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env))] 
        (map #(vector (search/node-str %) (reward-bounds %)) (take 80 (all-refinements node (make-queue-pq) (constantly 0)))))

(let [domain (make-nav-switch-strips-domain), env (constant-predicate-simplify (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4])), node (make-initial-alt-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env) )] (time (second (a-star-search node))))
;(interactive-search node (make-queue-pq) (constantly 0)))

(u util envs search search.algorithms.textbook angelic angelic.hierarchies domains.nav-switch domains.strips angelic.hierarchies.strips-hierarchies util.queues domains.warehouse)

; Flat hierarchies
(let [env (make-nav-switch-env 6 6 [[1 1]] [5 0] true [0 5]), node (make-initial-alt-node :edu.berkeley.ai.angelic/ExplicitValuation (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 4))))) ) env))] (time (second (a-star-search node))))

(let [env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]), node (make-initial-alt-node  :edu.berkeley.ai.angelic/ExplicitValuation (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env))] (time (second (a-star-search node))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]),  node (make-initial-alt-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env))] (time (second (a-star-search node))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]),  node (make-initial-alt-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0) ) env))] (time (second (a-star-search node))))



(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]])),  node (make-initial-alt-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env))] (time (second (a-star-search node))))

(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (make-initial-alt-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" (make-warehouse-strips-domain)) env))] (time (second (a-star-search node))))

(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (alt-node (get-hierarchy  "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" env))] (time (second (a-star-search node))))

  )




