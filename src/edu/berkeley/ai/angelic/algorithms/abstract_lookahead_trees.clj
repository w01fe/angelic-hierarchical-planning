(ns edu.berkeley.ai.angelic.algorithms.abstract-lookahead-trees
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap Map$Entry HashSet])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.graphs :as graphs]
	    [edu.berkeley.ai.util.graphviz :as graphviz]))



;; Abstract lookahead trees, with (optional) forward caching and graph stuff.

; TODO: caching prevents garbage collection; should use Apache ReferenceMap with weak/soft values 

; WARNING: can't reuse this (when graph?) or will end up with bad results... possible
 ; failure, or suboptimal plans...

; recheck-graph? option makes check for pruning on expansion as well as storage 
 ; -- otherwise, can end up with no pruning at all (?)  
 ; Will only happen when we get unlucky ? 

; Note: msut be very careful about eliminating duplicate plans; can
;  also create cycles.  Thus, it's only turned on when we're using graph
; style that never prunes weakly on non-live nodes.
 ; Why don't we just add an edge, exactly ?  Well, then we have to keep trakc
   ; of set of final nodes at each point, possibly add mulitple edges, etc.  
   ; And, in current hierarchies, shouldn't happen (why does it?)

; An interesting, efficiently checkable condition is whether any ancestor of a given HLA has made
; a non-vacuous pessimistic claim.  If not, you can prune strictly on anything.
  ; but is it correct ??
  ; In fact, while it doesn't change the # of refinements (AT ALL), it does make runtime 2x faster
   ; on (*icaps-ww* 4).... seems it's just since it avoids DAG calls.  

;; Beware of real-valued costs; rounding error + pruning can result in suboptimality/incompleteness.

;; TODO: should handle duplicate plans properly in full graph.

;; ALTs, nodes, and plans

(defstruct abstract-lookahead-tree :cache? :graph? :recheck-graph? :ref-choice-fn :subsumption-info :arg-map)
(defn- make-alt [cache? graph? recheck-graph? ref-choice-fn subsumption-info arg-map]
  (with-meta 
    (struct abstract-lookahead-tree cache? graph?  recheck-graph? ref-choice-fn subsumption-info arg-map)
    {:graph-map (HashMap.)
     :live-set  (HashSet.)
     :ancestor-graph (util/sref (graphs/make-empty-dag))
     :node-counter (util/counter-from 0)}))

;(util/defvar- *always-live* -1)

(derive ::ALTPlanNode ::search/Node)
(defstruct alt-plan-node :class :alt :name :plan :depth)
(defn make-alt-plan-node [class alt name plan depth]
  (let [final-ref (:was-final? ^plan)]
    (when (util/sref-get final-ref)
      (util/print-debug 2 "Warning: duplicate plan ... " (search/node-str {:class ::ALTPlanNode :plan plan}))
    #_  (throw (Exception.))) 
    (util/sref-set! final-ref true))
  (struct alt-plan-node class alt name plan depth))

; was-tight? tells whether some ancestor HLA made non-vacuous pessimistic claim.
(defstruct alt-action-node :hla :previous :primitive?)
(defn make-alt-node [hla previous-node was-tight? opt-val pess-val] 
  (with-meta  
   (struct alt-action-node hla previous-node 
	   (or (not previous-node) 
	       (and (util/safe-get previous-node :primitive?)
		    (hla-primitive? hla)))) 
   {:pessimistic-valuation (util/sref pess-val), :optimistic-valuation (util/sref opt-val)
    :cache (HashMap.) :fate (util/sref nil)
    :was-tight? was-tight? :was-final? (util/sref false)
    }))
; Fate can be nil, :refined, :pruned; for visualizing only.

(defn get-alt-node [alt hla previous-node was-tight?] "Returns a cached node if available."
  (let [#^HashMap cache (when (util/safe-get alt :cache?) (util/safe-get ^previous-node :cache))]
    (or (and cache (.get cache hla))
	(let [ret (make-alt-node hla previous-node was-tight? nil nil)]
	  (when cache (.put cache hla ret))
	  ret))))



;; Internal methods

(defn do-restrict-valuation-alt [x y]
  (restrict-valuation x y))


(defn pessimistic-valuation [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *pp-counter* inc)
	      (progress-valuation 
	       (do-restrict-valuation-alt (pessimistic-valuation (:previous node)) 
					  (hla-hierarchical-preconditions (:hla node)))
	       (hla-pessimistic-description (:hla node))))))))


(defn optimistic-valuation [node]
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (do (util/sref-up! *op-counter* inc)
;	      (println "Progress-optimistic" 
;	               (optimistic-valuation (:previous node))
;		       (hla-hierarchical-preconditions (:hla node))
;		       (hla-name (:hla node)))
	      (progress-valuation 
	       (do-restrict-valuation-alt (optimistic-valuation (:previous node))
					  (hla-hierarchical-preconditions (:hla node)))
	       (hla-optimistic-description (:hla node))))))))


;; Choice functions, used by search algorithms

(defn first-choice-fn [node]
  (let [plan (:plan node)]
    (when-not (util/safe-get plan :primitive?)
      (first (drop-while #(not (:primitive? (:previous %)))
			 (iterate :previous plan))))))
;  (loop [node (:plan node) cur nil]
;    (if (:previous node)
;        (recur (:previous node) (if (hla-primitive? (:hla node)) cur node))
;      cur)))

(defn last-choice-fn [node]
  (loop [node (:plan node)]
    (when (:previous node)
      (if (hla-primitive? (:hla node)) (recur (:previous node)) node))))

(defn make-first-maximal-choice-fn [level-map]
  (fn [node]
    (loop [node (:plan node), cur nil, max-level Double/NEGATIVE_INFINITY]
      (if-let [prev (:previous node)]
          (if (hla-primitive? (:hla node)) 
  	      (recur prev cur max-level)
  	    (let [n (first (hla-name (:hla node)))
		  level (util/lazy-get level-map n (do (println "WARNING: no level for " n) 0))]
	      (if (>= level max-level) 
 	          (recur prev node (double level))
	        (recur prev cur max-level))))
        cur))))


; Like ICAPS, but weights exponentially towards earlier actions.
(defn make-weighted-icaps-choice-fn [weight]
  (let [weight (double weight)]
   (fn [node]
    (loop [node (:plan node), cur nil, maxgap Double/NEGATIVE_INFINITY]
      (if-let [prev (:previous node)]
          (if (hla-primitive? (:hla node)) (recur prev cur (/ maxgap weight))
            (let [opt      (- (valuation-max-reward (optimistic-valuation node))
			      (valuation-max-reward (optimistic-valuation prev)))
		  mypess   (valuation-max-reward (pessimistic-valuation node))
		  prevpess (valuation-max-reward (pessimistic-valuation prev))
		  pess     (if (> prevpess Double/NEGATIVE_INFINITY)
			     (- mypess prevpess)
			     Double/NEGATIVE_INFINITY)
		  gap      (- opt pess)]
;	  (println (hla-name (:hla node)) gap opt pess mypess prevpess)
	      (if (>= gap maxgap)
	          (recur prev node (/ (double gap) weight))
		(recur prev cur (/ maxgap weight)))))
	cur)))))

; Almost icaps, except tiebreaks towards earlier, not higher-level...
(def icaps-choice-fn 
  (make-weighted-icaps-choice-fn 1))


; Choose the first HLA with nonzero gap, or first HLA if no gap.
(defn first-gap-choice-fn [node]
  (loop [node (:plan node), cur nil, cur-gap? true]
    (if-let [prev (:previous node)]
      (if (hla-primitive? (:hla node)) (recur prev cur cur-gap?)
	  (let [opt    (valuation-max-reward (optimistic-valuation node))
		pess   (valuation-max-reward (pessimistic-valuation node))
		gap?   (> opt pess)]
	    (when gap? (util/assert-is (identity cur-gap?)))
	    (if (and cur-gap? cur (not gap?)) 
	        cur
	      (recur prev node gap?))))
      cur)))


; Sometimes this priority fn misguides us ... pessimistic desc. too pessimistic...
(defn icaps-priority-fn [node]  
;  (println (map hla-name (map :hla (butlast (util/iterate-while :previous (:plan node)))))); (search/node-str node))
  (loop [nd (util/safe-get node :plan), 
	 upper (search/upper-reward-bound node),
	 lower (search/lower-reward-bound node),
	 p 0]
    (if (nil? (:previous nd)) p
	(let [prev (:previous nd)
	      prev-upper (valuation-max-reward (optimistic-valuation prev))
	      prev-lower (valuation-max-reward (pessimistic-valuation prev))
	      opt  (- upper prev-upper)
	      pess (- lower prev-lower)
	      name (hla-name (:hla nd))
	      act? (or (= 'act name) (and (coll? name) (= 'act (first name))))]
	  (recur prev prev-upper prev-lower
		 (- p 
		    (max (/ (+ opt pess) 2)
			 (if act?
			   (min -1 (* 3 opt))
			   (* 1.5 opt)))))))))

(defn get-weighted-aha-star-priority-fn [wt]
  (fn [node]  
    (loop [nd (util/safe-get node :plan), 
	   upper (search/upper-reward-bound node),
	   lower (search/lower-reward-bound node),
	   p 0]
      (if (nil? (:previous nd)) p
	  (let [prev (:previous nd)
		prev-upper (valuation-max-reward (optimistic-valuation prev))
		prev-lower (valuation-max-reward (pessimistic-valuation prev))
		opt  (- upper prev-upper)
		pess (- lower prev-lower)
	;	act? (= 'act (first (hla-name (:hla nd))))
		]
;	    (println upper lower prev-upper prev-lower opt pess act?)
	    (recur prev prev-upper prev-lower
		   (- p 
		      (max pess (* wt opt)))))))))


;; Constructing initial nodes


(defn make-alt-root-node [alt opt-val pess-val]
  (make-alt-node :root nil false opt-val pess-val))

(declare graph-add-and-check!)

(util/defn-opt make-initial-alt-node 
  [initial-plan & 
    node-type ::ALTPlanNode, ref-choice-fn first-gap-choice-fn,
    cache? true, graph? true, recheck-graph? false, 
    subsumption-info {}, valuation-class nil, 
    opt-valuation-class (or valuation-class (hla-default-optimistic-valuation-type (first initial-plan)))
    pess-valuation-class (or valuation-class (hla-default-pessimistic-valuation-type (first initial-plan))),
    arg-map]
  (util/assert-is (contains? #{true false :full :simple :bhaskara :icaps08} graph?))
  (util/assert-is (fn? ref-choice-fn))
  (when recheck-graph? (assert graph?))
  (let [env (hla-environment (first initial-plan)), 
	alt (make-alt cache? graph? recheck-graph? ref-choice-fn subsumption-info arg-map)
	root (make-alt-root-node alt 
		     (state->valuation opt-valuation-class (envs/get-initial-state env))
		     (state->valuation pess-valuation-class (envs/get-initial-state env)))
	name ((:node-counter ^alt))]
    (when graph? (assert (graph-add-and-check! alt root initial-plan name))) ;*always-live*)))
 ;   (println (:graph-map ^alt))
;    (.add #^HashSet (:live-set ^alt) *always-live*)
    (.add #^HashSet (:live-set ^alt) name)
    (loop [actions initial-plan
	   previous root]
      (if (empty? actions)
          (make-alt-plan-node node-type alt name previous 0)
	(recur (next actions)
	       (get-alt-node alt (first actions) previous false))))))

(defn alt-node [& args] (apply make-initial-alt-node args))



;; Graph stuff

(def *dummy-pair-alt* [Double/NEGATIVE_INFINITY (gensym)])

(defn test-and-add-edge! "Returns true iff edge added." [alt from to]
  (let [ancestor-graph-ref (util/safe-get ^alt :ancestor-graph)]
;    (println (util/sref-get ancestor-graph-ref) from to)
    (when-not (graphs/dag-descendant? (util/sref-get ancestor-graph-ref) to from)
      (util/sref-up! ancestor-graph-ref #(graphs/dag-add-edge % from to))
      true)))

; Right now, subsumption only good for ignoring irrelevant predicates.

(defn add-node-pruning-info! [alt node rest-plan name]
  (util/assert-is (:graph? alt))
  (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	subsumption-info    (util/safe-get alt :subsumption-info)
	pess-val              (pessimistic-valuation node)]
    (when-not (empty-valuation? pess-val) 
      (let [[pess-states pess-si] (get-valuation-states pess-val subsumption-info)
	    pair [pess-states rest-plan]
	    graph-tuples          (.get graph-map pair)]
	(when (every?
	       (fn [[graph-si graph-node]]
		 (not (#{:strict :weak} (valuation-subsumes? graph-si pess-si subsumption-info))))
	       graph-tuples)
	  (.put graph-map pair
		(cons [pess-si name node]
		      (remove
		       (fn [[graph-si graph-node]]
			 (valuation-subsumes? pess-si graph-si subsumption-info))
		       graph-tuples))))))))
 

(defn node-prunable? [alt node rest-plan name]
  (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	#^HashSet live-set  (util/safe-get ^alt :live-set)
	subsumption-info    (util/safe-get alt :subsumption-info)
	opt-val             (optimistic-valuation node)
	[opt-states opt-si] (get-valuation-states opt-val subsumption-info)
	graph-tuples        (.get graph-map [opt-states rest-plan])]
;   (println (count graph-tuples) (:graph? alt) (:class opt-val))
   (when-let [[bad-si bad-name bad-node]
	 (util/find-first  ; TODO: find first, weakest ?  But then make sure not to add extra edges...
	   (fn [[graph-si graph-node]]
	     (let [subsumes? (valuation-subsumes? graph-si opt-si subsumption-info)] 
;	       (println "AAA" graph-node name)
	       (not (or (= graph-node name)
		        (and (= (:graph? alt) :icaps08) (not (.contains live-set graph-node)))
			(not subsumes?)
			(and (not (= subsumes? :strict))
			     (or (= (:graph? alt) :bhaskara) 
				 (and (= (:graph? alt) :simple) (not (.contains live-set graph-node)))
				 (and (= (:graph? alt) true) (util/safe-get ^node :was-tight?) 
				      (not (.contains live-set graph-node)))
				 (and (= (:graph? alt) :full)
				      (util/safe-get ^node :was-tight?) 
				      (not (test-and-add-edge! alt graph-node name)))))))))
	   graph-tuples)]
        (util/sref-set! (:fate ^node) bad-node)
	true)))


(defn plan-prunable? [alt plan]
  (let [name (util/safe-get plan :name)]
    (loop [node (util/safe-get plan :plan) rest-plan nil]
      (or ;(println name (map hla-name rest-plan))
          (and (node-prunable? alt node rest-plan name)
	       (do (util/print-debug 3 "Secondary pruning at " 
				 (search/node-str {:class ::ALTPlanNode :plan node})
				 (map hla-name rest-plan))
	       true))
	  (when-let [previous (util/safe-get node :previous)]
	    (recur previous (cons (util/safe-get node :hla) rest-plan)))))))

(defn graph-add-and-check! [alt node rest-plan name]
;  (println "GAC" (map hla-name rest-plan))
  (when-not (node-prunable? alt node rest-plan name)
    (add-node-pruning-info! alt node rest-plan name)
    true))



	       

;; Node methods 
(declare construct-immediate-refinement)
(defmethod search/reroot-at-node ::ALTPlanNode [node & args]
  (let [alt (:alt node)
	#^HashMap cache (:graph-map ^alt)
	#^HashSet live-set (:live-set ^alt)
	name   (util/safe-get node :name)]
    (.clear live-set)
    (.clear cache)
    (util/sref-set! (:ancestor-graph ^alt) (graphs/make-empty-dag))
;    (when (:graph? alt)
;      (loop [node (:plan node), plan nil]
;	(when node
;	  (graph-add-and-check! alt node plan name)
;	  (recur (:previous node) (cons (:hla node) plan)))))
    (.add live-set name)
;    (println "refs " (util/sref-get search/*ref-counter*))
;    (println (first args))
;    (println (:ref-choice-fn (:alt node)))
    (construct-immediate-refinement node 
				    (vary-meta (last (util/iterate-while :previous (:plan node))) assoc :cache (HashMap.))
				    (map :hla (next (reverse (util/iterate-while :previous (:plan node))))) 
				    (if (seq args) (assoc (:alt node) :ref-choice-fn (first args)) (:alt node)) 0
				    name false)))
;    (if (seq args)
;        (assoc node :alt (assoc (:alt node) :ref-choice-fn (first args)))
;      node)))
;  (.clear 



(defmethod search/node-environment   ::ALTPlanNode [node] (hla-environment (:hla (:plan node))))

(defmethod search/node-state         ::ALTPlanNode [node]
  (if (nil? (:previous (:previous (:plan node))))
      (envs/get-initial-state (hla-environment (:hla (:plan node))))
    (throw (IllegalArgumentException.))))

(defmethod search/lower-reward-bound ::ALTPlanNode [node] 
  (valuation-max-reward (pessimistic-valuation (:plan node))))

(defmethod search/upper-reward-bound ::ALTPlanNode [node] 
  (valuation-max-reward (optimistic-valuation (:plan node))))


(defmethod search/reward-so-far ::ALTPlanNode [node] 0)

(defmulti construct-immediate-refinement (fn [node previous actions alt parent-depth name was-tight?] (:class node)))
(defmethod construct-immediate-refinement ::ALTPlanNode [node previous actions alt parent-depth name was-tight?]
  (if (empty? actions) 
    (make-alt-plan-node (:class node) alt name previous (inc parent-depth) )
    (let [nxt (get-alt-node alt (first actions) previous was-tight?)]
      (if (and (or (not (empty-valuation? (optimistic-valuation nxt)))
		   (and (util/sref-set! (:fate ^nxt) :dead) false))
	       (or (next actions) 
		   (not (util/sref-get (:was-final? ^nxt)))
		   (= :full (:graph? alt))) ; Eliminate duplicates.
	       (or (not (:graph? alt)) 
		   (graph-add-and-check! alt nxt (next actions) 
					 name)))
	  (recur node nxt (next actions) alt parent-depth name was-tight?)
	(util/print-debug 3 "Late prune at" (search/node-str {:class ::ALTPlanNode :plan nxt})
			  (map hla-name (next actions))
			  ;(map println (map optimistic-valuation (util/iterate-while :previous nxt)))
;			  (optimistic-valuation (:previous (:previous nxt)))
			  )))))

(defmethod search/immediate-refinements ::ALTPlanNode [node] 
  (util/timeout)
  (let [urb         (search/upper-reward-bound node)
	alt         (util/safe-get node :alt)
	graph?      (util/safe-get alt :graph?)
	plan        (:plan node)
	ref-node    ((util/safe-get alt :ref-choice-fn) node)]
    (when ref-node 
      (util/print-debug 3  "About to refine " (search/node-str node) " at " (hla-name (:hla ref-node))))
    (when (and ref-node
	       (or (not (util/safe-get alt :recheck-graph?))
		   (not (when (plan-prunable? alt node) 
			       (util/print-debug 3 "Secondary pruning at recheck!")
			       true))))
     ;; If ref-fn is correct, == when not fully primitive
      (util/sref-up! search/*ref-counter* inc)
      (let [was-tight?  (and (contains? #{true :full} graph?) 
			 (or (util/safe-get ^ref-node :was-tight?)
			     (not (empty-valuation? (pessimistic-valuation ref-node)))))
			  ;   (= (valuation-max-reward (optimistic-valuation ref-node))
			  ;	(valuation-max-reward (pessimistic-valuation ref-node)))))
	    after-actions  (map :hla (reverse (take-while #(not (identical? % ref-node)) 
							  (iterate :previous plan))))]
	(when graph? (.remove #^HashSet (:live-set ^alt) (util/safe-get node :name)))
	(util/sref-set! (:fate ^ref-node) :refined)
;	(println (count (hla-immediate-refinements (:hla ref-node) (optimistic-valuation (:previous ref-node)))))
	(filter identity
	 (for [ref (hla-immediate-refinements (:hla ref-node) (optimistic-valuation (:previous ref-node)))]
	   (let [name         ((:node-counter ^alt))]
  	     (util/print-debug 3 "\nConsidering refinement " (map hla-name ref) " at " (hla-name (:hla ref-node)))
	     (util/sref-up! search/*plan-counter* inc)
	     (when (= graph? :full)
	       (assert (test-and-add-edge! alt name (util/safe-get node :name))))
	     (when-let [nxt (construct-immediate-refinement node (:previous ref-node) (concat ref after-actions) alt (util/safe-get node :depth) name was-tight?)]
	       (when graph? (.add #^HashSet (:live-set ^alt) name))
;		 (when (> (search/upper-reward-bound nxt) urb) 
;		   (util/sref-set! (:upper-reward-bound ^(:plan nxt)) urb)
;		   (println "Fixing Upper Inconcistency" urb (search/upper-reward-bound nxt)))
	       nxt))))))))


(defmethod search/primitive-refinement ::ALTPlanNode [node]
  (let [node (:plan node)]
    (when (util/safe-get node :primitive?)
      (let [act-seq (remove #(= % :noop)
		      (map (comp hla-primitive :hla) (next (reverse (util/iterate-while :previous node))))) 
	    upper (valuation-max-reward (optimistic-valuation node))] 
	[act-seq upper]))))

(defmethod search/extract-optimal-solution ::ALTPlanNode [node] 
  (when (and (util/safe-get-in node [:plan :primitive?]) 
	     (> (search/upper-reward-bound node) Double/NEGATIVE_INFINITY))
    (search/primitive-refinement node)))

(defn fancy-node-str [node] 
  (util/str-join " " 
    (map (fn [n] [(hla-name (:hla n)) [(valuation-max-reward (pessimistic-valuation n))
				       (valuation-max-reward (optimistic-valuation n))]])
	 (next (reverse (util/iterate-while :previous (:plan node)))))))

(defmethod search/node-str ::ALTPlanNode [node] (fancy-node-str node))
;  (util/str-join " " (map (comp hla-name :hla) (next (reverse (util/iterate-while :previous (:plan node)))))))

(defmethod search/node-plan ::ALTPlanNode [node]
  (map :hla (rest (reverse (util/iterate-while :previous (:plan node))))))

(defmethod search/node-first-action ::ALTPlanNode [node]
  (let [first-node (last (butlast (util/iterate-while :previous (:plan node))))
	first-hla  (:hla first-node)]
    (hla-primitive first-hla)))

(defmethod search/node-plan-length ::ALTPlanNode [node]
  (dec (count (util/iterate-while :previous (:plan node)))))

(defmethod search/node-depth ::ALTPlanNode [node]
  (util/safe-get node :depth))

(defn alt-node-hla-count  [node]
  (count (remove #(hla-primitive? (:hla %)) (butlast (util/iterate-while :previous (:plan node))))))


;;; For ICAPS07 algorithm, and perhaps other uses

(defn state->condition [state instance]
  (let [all-atoms (util/to-set (util/safe-get (envs/get-state-space instance) :vars))]
    (envs/make-conjunctive-condition state (util/difference all-atoms state))))

(defn extract-state-seq [plan state-seq]
;  (println "ESS" (count state-seq) (first state-seq))
  (if (nil? (:previous plan))
      state-seq
    (recur (:previous plan)
	   (cons
	    (first
	     (util/make-safe
	      (regress-state (first state-seq)
			     (pessimistic-valuation       (:previous plan))
			     (hla-pessimistic-description (:hla plan))
			     (pessimistic-valuation       plan))))
	    state-seq))))

(defn decompose-plan
  "Take a node corresponding to a pessimistically succeeding plan, and return a 
   sequence of fresh nodes corresponding to the subproblem of finding a primitive refinement of that
   particular action."
  [node]
  (util/assert-is (> (search/lower-reward-bound node) Double/NEGATIVE_INFINITY))
  (let [env       (hla-environment (:hla (:plan node)))
	state-seq (extract-state-seq (:plan node) 
				     [(first (valuation-max-reward-state (pessimistic-valuation (:plan node))))])
	alt       (util/safe-get node :alt)]
  ;  (println "decomposing " (search/node-str node) " on \n" (util/str-join "\n\n" (map #(envs/state-str env %) state-seq)))
    (util/assert-is (= (first state-seq) (envs/get-initial-state env)))
;    (util/assert-is (envs/satisfies-condition? (last state-seq) (envs/get-goal env)))
    (map 
     (fn [[s s2] a] 
       (make-initial-alt-node 
	(edu.berkeley.ai.angelic.hierarchies.strips-hierarchies/sub-environment-hla 
	  (:hla a) s (state->condition s2 env))
	(util/safe-get alt :arg-map)))
     (partition 2 1 state-seq)
     (rest (reverse (util/iterate-while :previous (:plan node)))))))



(defn graphviz-alt [node]
  (graphviz/write-graphviz "/tmp/alt.pdf"
   [(last (util/iterate-while :previous (:plan node))) false]
   (fn [[n r]] n) ;(:name n))
   (fn [[n r?]] 
     (let [fate (util/sref-get (:fate ^n))]
       {:label (util/double-quote [(valuation-max-reward (pessimistic-valuation n))
				   (valuation-max-reward (optimistic-valuation n))])
	:color (cond 
		 r? "blue"
		 (and fate (not (= :refined fate))) "red" 
		 :else "black")}))
   (fn [[n r?]] 
     (let [parent-fate (util/sref-get (:fate ^n))]
       (if (and parent-fate (not (= parent-fate :refined)) (not (= parent-fate :dead)))
	   (do (assert (empty? (:cache ^n)))
	       [[{:color "red"} [parent-fate false]]])
     (for [[e n] (:cache ^n)]
       (let [fate (util/sref-get (:fate ^n))]
	 [{:label (util/double-quote (hla-name e)) 
	   :color (if (= :refined fate) "blue" "black")}  
	  [n (or r? (= :refined fate))]]))))))
  (util/sh "open" "-a" "Skim" "/tmp/alt.pdf"))


(defn graphviz-alt2 
  ([nodes] (graphviz-alt2 nodes true true true))
  ([nodes show-finish show-refined show-noop]
  (doseq [node nodes,
	  n (util/iterate-while :previous (:plan node))]
    (assert (contains? #{nil :live} (util/sref-get (:fate ^n))))
    (util/sref-set! (:fate ^n) :live))
  (graphviz/write-graphviz "/tmp/alt.pdf"
   (last (util/iterate-while :previous (:plan (first nodes))))
   identity
   (fn [n] 
;     (if (isa? (:class n) ::ALTPlanNode)
;         {:label (util/double-quote [(search/lower-reward-bound n)
;				     (search/upper-reward-bound n)])
;	  :color "green"}
       (let [fate (util/sref-get (:fate ^n))]
;	 (println fate)
	 {:label (util/double-quote [(valuation-max-reward (pessimistic-valuation n))
				     (valuation-max-reward (optimistic-valuation n))])
	  :color (cond 
		   (= :live fate) "green"
		   (and fate (not (= :refined fate))) "red" 
		   :else "black")}));)
   (fn [n] 
     (when-not (isa? (:class n) ::ALTPlanNode)
     (let [parent-fate (util/sref-get (:fate ^n))]
       (cond (and parent-fate (not (= parent-fate :refined)) (not (= parent-fate :dead)) (not (= parent-fate :live)))
  	       (do (assert (empty? (:cache ^n)))
		   [[{:color "red" :style "dotted"} parent-fate]])
	     ;(and (= parent-fate :live) (empty? (:cache ^n)))
	     ;  (let [final (util/make-safe (util/find-first #(identical? (:plan %) n) nodes))]
	     ;   [[{:label (util/double-quote "[finish]") :color "green"} final]])
	     :else
	       (for [[e n] (:cache ^n) :when (and (or show-finish (not (.startsWith (str (hla-name e)) "[finish")))
						  (or show-refined (not (= :refined (util/sref-get (:fate ^n)))))
						  (or show-noop (not (.startsWith (str (hla-name e)) "[noop"))))]
		 (let [fate (util/sref-get (:fate ^n))]
		   [{:label (util/double-quote (hla-name e)) 
		     :color (condp = fate :refined "blue" :live "green" "black")}  
		    n])))))))
  (doseq [node nodes,
	  n (util/iterate-while :previous (:plan node))]
    (util/sref-set! (:fate ^n) nil))
  (util/sh "open" "-a" "Skim" "/tmp/alt.pdf")
  ))









	    









(comment ; Version with subsumption, didn't help, so taken out for now.




; Old version, no subsumption
(defn graph-add-and-check! [alt node rest-plan name]
  (util/assert-is (:graph? alt))
  (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	#^HashSet live-set  (util/safe-get ^alt :live-set)
	subsumption-info    (util/safe-get alt :subsumption-info)
	opt-val    (optimistic-valuation node)
	[opt-states] (get-valuation-states opt-val subsumption-info)
	opt-rew    (valuation-max-reward opt-val)
	[graph-rew graph-node]  (or (.get graph-map [opt-states rest-plan]) *dummy-pair-alt*)]
;	(when (not (or (> opt-rew graph-rew) (and (= opt-rew graph-rew) (contains? ancestor-set graph-node))))
;	  (println "pruning!" name ancestor-set graph-node graph-rew opt-rew (contains? ancestor-set graph-node)))
    (when (or (and (= (:graph? alt) :old) (not (.contains live-set graph-node)))
	      (> opt-rew graph-rew)
	      (and (not (.contains live-set graph-node))
		   (= opt-rew graph-rew)))
      (let [pess-val    (pessimistic-valuation node)
	    pess-rew    (valuation-max-reward pess-val)
	    [pess-states] (get-valuation-states pess-val subsumption-info)
	    pair        [pess-states rest-plan]
	    [graph-rew graph-node] (or (.get graph-map pair) *dummy-pair-alt*)]
	(when (>= pess-rew graph-rew)
	  (.put graph-map pair [pess-rew name])))
      true)))

)


