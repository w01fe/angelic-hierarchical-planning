(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap Map$Entry])
  (:require [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv]
            [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]))



;; Abstract lookahead trees, with (optional) forward caching and graph stuff.

; WARNING: plan-Graph search will not work here!  Cannot eliminate duplicate plans due to
; iteraction with state-graph..

; WARNING: can't reuse this (when graph true) or will end up with bad results... possible
 ; failure, or suboptimal plans...

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
; Strengths: as much pruning as possible, multi-generated plans automatically pruned
; Weaknesses: must keep track of ancestors, may multi-generate plans. Replacement policy? Always replace.
;              fails if inconsistent ???

; TODO: add consistency check?


;; ALTs, nodes, and plans

(defstruct abstract-lookahead-tree :cache? :graph? :goal :ref-choice-fn)
(defn- make-alt [cache? graph? goal ref-choice-fn]
  (with-meta 
    (struct abstract-lookahead-tree cache? graph? goal ref-choice-fn)
    {:graph-map (HashMap.)}))

(derive ::ALTPlanNode ::search/Node)
(defstruct alt-plan-node :class :alt :name :plan :ancestor-set)
(defn make-alt-plan-node [alt name plan ancestor-set]
  (struct alt-plan-node ::ALTPlanNode alt name plan ancestor-set))

(defstruct alt-action-node :hla :previous)
(defn make-alt-node [hla previous-node opt-val pess-val] 
  (with-meta  
   (struct alt-action-node hla previous-node) 
   {:pessimistic-valuation (util/sref pess-val), :optimistic-valuation (util/sref opt-val)
    :lower-reward-bound (util/sref nil) :upper-reward-bound (util/sref nil) :cache (HashMap.)}))

(defn get-alt-node [alt hla previous-node]
  (let [#^HashMap cache (when (util/safe-get alt :cache?) (util/safe-get ^previous-node :cache))]
    (or (when cache (.get cache hla))
	(let [ret (make-alt-node hla previous-node nil nil)]
	  (when cache (.put cache hla ret))
	  ret))))



;; Internal methods

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


;; Choice functions, used by search algorithms

(defn- first-choice-fn [node]
  (loop [node (:plan node) cur nil]
    (if (:previous node)
        (recur (:previous node) (if (hla-primitive? (:hla node)) cur node))
      cur)))

(defn- last-choice-fn [node]
  (loop [node (:plan node)]
    (when (:previous node)
      (if (hla-primitive? (:hla node)) (recur (:previous node)) node))))

; Almost icaps, except tiebreaks towards earlier, not higher-level...
(defn- icaps-choice-fn [node]
  (loop [node (:plan node), cur nil, maxgap Double/NEGATIVE_INFINITY]
    (if-let [prev (:previous node)]
        (if (hla-primitive? (:hla node)) (recur prev cur maxgap)
        (let [opt      (- (get-valuation-upper-bound (optimistic-valuation node))
			  (get-valuation-upper-bound (optimistic-valuation prev)))
	      mypess   (get-valuation-lower-bound (pessimistic-valuation node))
	      prevpess (get-valuation-lower-bound (pessimistic-valuation prev))
	      pess     (if (> prevpess Double/NEGATIVE_INFINITY)
			   (- mypess prevpess)
			 Double/NEGATIVE_INFINITY)
	      gap      (- opt pess)]
;	  (println (hla-name (:hla node)) gap opt pess mypess prevpess)
	  (if (>= gap maxgap)
	      (recur prev node (double gap))
	    (recur prev cur maxgap))))
      cur)))


; Sometimes this priority fn misguides us ... pessimistic desc. too pessimistic...
(defn icaps-priority-fn [node]  
;  (println (map hla-name (map :hla (butlast (util/iterate-while :previous (:plan node)))))); (search/node-str node))
  (- 0
     (util/reduce-key + 
	(fn [node] 
	  (let [prev (:previous node)
		opt  (- (get-valuation-upper-bound (optimistic-valuation node))
			(get-valuation-upper-bound (optimistic-valuation prev)))
		pess (- (get-valuation-lower-bound (pessimistic-valuation node))
			(get-valuation-lower-bound (pessimistic-valuation prev)))
		act? (= '[act] (hla-name (:hla node)))]
	    (max (/ (+ opt pess) 2)
		 (if act?
		     (min -1 (* 3 opt))
		   (* 1.5 opt)))))
	(butlast (util/iterate-while :previous (util/safe-get node :plan))))))


;; Constructing initial nodes


(defn make-alt-root-node [alt initial-valuation]
  (make-alt-node :root nil initial-valuation initial-valuation))

(defn make-initial-alt-node 
  ([initial-node] (make-initial-alt-node initial-node true true))
  ([initial-node ref-choice-fn] (make-initial-alt-node initial-node ref-choice-fn true true))
  ([initial-node cache? graph?] (make-initial-alt-node initial-node first-choice-fn cache? graph?))
  ([initial-node ref-choice-fn cache? graph?] (make-initial-alt-node (hla-default-valuation-type initial-node) 
								     initial-node ref-choice-fn cache? graph?))
;  ([valuation-class initial-node] (make-initial-alt-node valuation-class initial-node true true))
  ([valuation-class initial-node ref-choice-fn cache? graph?]
  (util/assert-is (contains? #{true false :partial} graph?))
  (let [env (hla-environment initial-node), name (gensym)
	alt (make-alt cache? graph? (envs/get-goal env) ref-choice-fn)]
    (loop [actions (list initial-node)
	   previous (make-alt-root-node alt (make-initial-valuation valuation-class env))]
      (if (empty? actions)
          (make-alt-plan-node alt name previous #{})
	(recur (rest actions)
	       (get-alt-node alt (first actions) previous)))))))

(defn alt-node [& args] (apply make-initial-alt-node args))



;; Graph stuff

(def *dummy-pair-alt* [Double/NEGATIVE_INFINITY (gensym)])

; Return true if keep, false if prune.
(defn graph-add-and-check! [alt node rest-plan name ancestor-set]
  (util/assert-is (:graph? alt))
  (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	opt-val    (optimistic-valuation node)
	opt-states (get-valuation-states opt-val)
	opt-rew    (get-valuation-upper-bound opt-val)
	[graph-rew graph-node]  (or (.get graph-map [opt-states rest-plan]) *dummy-pair-alt*)]
;	(when (not (or (> opt-rew graph-rew) (and (= opt-rew graph-rew) (contains? ancestor-set graph-node))))
;	  (println "pruning!" name ancestor-set graph-node graph-rew opt-rew (contains? ancestor-set graph-node)))
    (when (or (> opt-rew graph-rew) (and (= opt-rew graph-rew) (contains? ancestor-set graph-node)))
      (let [pess-val    (pessimistic-valuation node)
	    pess-states (get-valuation-states pess-val)
	    pess-rew    (get-valuation-lower-bound pess-val)
	    pair        [pess-states rest-plan]
	    [graph-rew graph-node] (or (.get graph-map pair) *dummy-pair-alt*)]
	(when (>= pess-rew graph-rew)
	  (.put graph-map pair [pess-rew name])))
      true)))
	       
(set! *warn-on-reflection* true)
;; TODO: make a method
;; TODO: make more efficient
(defn clear-alt-graph-cache "Clear the cache of all but ancestors of node, and return a new node."
  [node]
  (let [alt (:alt node)
	#^HashMap cache (:graph-map ^alt)
	it (.iterator (.entrySet cache))
	name   (util/safe-get node :name)
	oldset (conj (util/safe-get node :ancestor-set) name)
	newset #{name}]
;    (println (.size cache))
    (while (.hasNext it)
      (let [#^Map$Entry next (.next it)
	    k    (.getKey next)
	    v    (.getValue next)
	    v-name (second v)]
	(if (contains? oldset v-name)
	    (.setValue next (assoc v 1 name))
	  (.remove it))))
 ;   (println (.size cache))
;    node));
    (make-alt-plan-node alt name (:plan node) newset)))
;  (.clear 
(set! *warn-on-reflection* false)



;; Node methods 

(defmethod search/node-environment   ::ALTPlanNode [node] (hla-environment (:hla (:plan node))))

(defmethod search/node-state         ::ALTPlanNode [node]
  (if (nil? (:previous (:previous (:plan node))))
      (envs/get-initial-state (hla-environment (:hla (:plan node))))
    (throw (IllegalArgumentException.))))

(defmethod search/lower-reward-bound ::ALTPlanNode [node] 
  (let [alt  (:alt node)
	node (:plan node)
	s (:lower-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (get-valuation-lower-bound (do-restrict-valuation-alt (pessimistic-valuation node) (:goal alt)))))))

(defmethod search/upper-reward-bound ::ALTPlanNode [node] 
  (let [alt (:alt node)
	node (:plan node)
	s (:upper-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
          (get-valuation-upper-bound (do-restrict-valuation-alt (optimistic-valuation node) (:goal alt)))))))

(defmethod search/reward-so-far ::ALTPlanNode [node] 0)

(defmethod search/immediate-refinements ::ALTPlanNode [node] 
  (util/timeout)
  (util/sref-set! *ref-counter* (inc (util/sref-get *ref-counter*)))
  (let [alt         (util/safe-get node :alt)
	graph?      (util/safe-get alt :graph?)
	full-graph? (and graph? (not (= graph? :partial)))
	plan        (:plan node)
	ref-node    ((util/safe-get alt :ref-choice-fn) node)]
    (when ref-node ;; If ref-fn is correct, == when not fully primitive
   ;   (println "About to refine " (search/node-str node) " at " (hla-name (:hla ref-node)))
      (let [after-actions  (map :hla (reverse (take-while #(not (identical? % ref-node)) 
							  (iterate :previous plan))))
	    before-nodes   (when full-graph? (reverse (util/iterate-while :previous plan)))
	    before-actions (map :hla (rest before-nodes))
	    ancestors      (conj (util/safe-get node :ancestor-set) (util/safe-get node :name))]
	(filter identity
	 (for [ref (hla-immediate-refinements (:hla ref-node) (optimistic-valuation (:previous ref-node)))]
	   (let [name         (gensym)
		 tail-actions (concat ref after-actions)
		 all-actions  (concat before-actions tail-actions)]
	     (if (every? (fn [[node rest-plan]]    ; full graph prefix check
			     (graph-add-and-check! alt node rest-plan name ancestors))
			   (map vector before-nodes (iterate rest all-actions)))
	       (loop [previous (:previous ref-node)
		      actions  tail-actions]
		 (if (empty? actions) 
		     (make-alt-plan-node alt name previous ancestors)
		   (let [next (get-alt-node alt (first actions) previous)]
		     (when (or (not graph?) 
			       (graph-add-and-check! alt next (rest actions) name ancestors))
		       (recur next (rest actions))))))
	       (println "early prune")
	       ))))))))


(defmethod search/primitive-refinement ::ALTPlanNode [node]
  (let [node (:plan node)]
    (when (every? (comp hla-primitive? :hla) (butlast (util/iterate-while :previous node)))
;    (println (search/node-str node))
    (let [act-seq (remove #(= % :noop)
		   (map (comp hla-primitive :hla) (rest (reverse (util/iterate-while :previous node))))) 
	  upper (get-valuation-upper-bound (optimistic-valuation node))] 
      [act-seq upper]))))

(defmethod search/extract-optimal-solution ::ALTPlanNode [node] 
  (when (> (search/upper-reward-bound node) Double/NEGATIVE_INFINITY)
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




