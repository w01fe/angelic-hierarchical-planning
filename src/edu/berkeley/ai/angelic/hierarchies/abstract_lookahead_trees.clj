(ns edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap Map$Entry HashSet])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]))



;; Abstract lookahead trees, with (optional) forward caching and graph stuff.

; TODO: caching prevents garbage collection; should use Apache ReferenceMap with weak/soft values 
; Note: behaves like plan "graph" when caching turned on.

; WARNING: can't reuse this (when graph?) or will end up with bad results... possible
 ; failure, or suboptimal plans...

; Graph map is metadata on ALT, maps from [state-set rest-plan] --> [pess-valuations]  (old: max-pess-reward).
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

; OK, this is subtly wrong:
; L ... Navigate Put-R guarantees costs for last 2
; L ... Nav      Put-R guarantees costs for last 2
; U ... Navigate Put-R guarantees costs for last 2
; U ... Nav      Put-R, now tight, pruned at nav from 2 steps above
; L ... Nav      Put-R, now tight, pruned at Put-R from 2 steps above

; The soluton is to prune strictly on live nodes, and non-strictly on everything else.
; This means we must maintain a live list, but no ancestor sets are needed.
; If you throw away a node without telling the ALT, all hell can break loose.

;; ALTs, nodes, and plans

(defstruct abstract-lookahead-tree :cache? :graph? :goal :ref-choice-fn :subsumption-info)
(defn- make-alt [cache? graph? goal ref-choice-fn subsumption-info]
  (with-meta 
    (struct abstract-lookahead-tree cache? graph? goal ref-choice-fn subsumption-info)
    {:graph-map (HashMap.)
     :live-set  (HashSet.)
     :node-counter (util/counter-from 0)}))

(derive ::ALTPlanNode ::search/Node)
(defstruct alt-plan-node :class :alt :name :plan)
(defn make-alt-plan-node [class alt name plan]
  (struct alt-plan-node class alt name plan))

(defstruct alt-action-node :hla :previous :primitive?)
(defn make-alt-node [hla previous-node opt-val pess-val] 
  (with-meta  
   (struct alt-action-node hla previous-node 
	   (or (not previous-node) 
	       (and (util/safe-get previous-node :primitive?)
		    (hla-primitive? hla)))) 
   {:pessimistic-valuation (util/sref pess-val), :optimistic-valuation (util/sref opt-val)
    :lower-reward-bound (util/sref nil) :upper-reward-bound (util/sref nil) 
    :cache (HashMap.) :fate (util/sref nil)}))
; Fate can be nil, :refined, :pruned; for visualizing only.

(defn get-alt-node [alt hla previous-node] "Returns [node cached?]"
  (let [#^HashMap cache (when (util/safe-get alt :cache?) (util/safe-get ^previous-node :cache))]
    (or (when-let [n (and cache (.get cache hla))] [n true])
	(let [ret (make-alt-node hla previous-node nil nil)]
	  (when cache (.put cache hla ret))
	  [ret false]))))



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
	      act? (= 'act (first (hla-name (:hla nd))))]
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
		act? (= 'act (first (hla-name (:hla nd))))]
;	    (println upper lower prev-upper prev-lower opt pess act?)
	    (recur prev prev-upper prev-lower
		   (- p 
		      (max pess (* wt opt)))))))))


;; Constructing initial nodes


(defn make-alt-root-node [alt opt-val pess-val]
  (make-alt-node :root nil opt-val pess-val))

(declare graph-add-and-check!)
(defn make-initial-alt-node 
  ([initial-node] 
     (make-initial-alt-node initial-node true true))
  ([initial-node ref-choice-fn] 
     (make-initial-alt-node initial-node ref-choice-fn true true))
  ([initial-node cache? graph?] 
     (make-initial-alt-node initial-node first-choice-fn cache? graph?))
  ([initial-node ref-choice-fn cache? graph?] 
     (make-initial-alt-node initial-node {} ref-choice-fn cache? graph?))
  ([initial-node subsumption-info ref-choice-fn cache? graph?] 
     (make-initial-alt-node 
      (hla-default-optimistic-valuation-type initial-node)
      (hla-default-pessimistic-valuation-type initial-node)
      subsumption-info initial-node ref-choice-fn cache? graph?))
  ([valuation-class subsumption-info initial-node ref-choice-fn cache? graph?]
     (make-initial-alt-node valuation-class valuation-class subsumption-info initial-node ref-choice-fn cache? graph?))
  ([opt-valuation-class pess-valuation-class subsumption-info initial-node ref-choice-fn cache? graph?]

     (make-initial-alt-node ::ALTPlanNode opt-valuation-class pess-valuation-class subsumption-info initial-node ref-choice-fn cache? graph?))
 ([node-type opt-valuation-class pess-valuation-class subsumption-info initial-node ref-choice-fn cache? graph?]
;  (util/assert-is (empty? subsumption-info)) ;; Taken out for now. TODO
  (util/assert-is (contains? #{true false :full :bhaskara :icaps08 :sloppy} graph?))
  (let [initial-plan (list initial-node) ;(if (seq? initial-node) initial-node (list initial-node))
	env (hla-environment (first initial-plan)), 
	alt (make-alt cache? graph? (envs/get-goal env) ref-choice-fn subsumption-info)
	dummy-name ((:node-counter ^alt))
	root (make-alt-root-node alt 
		     (state->valuation opt-valuation-class (envs/get-initial-state env))
		     (state->valuation pess-valuation-class (envs/get-initial-state env)))
	name ((:node-counter ^alt))]
    (util/assert-is (graph-add-and-check! alt root initial-plan dummy-name)  )
 ;   (println (:graph-map ^alt))
    (.add #^HashSet (:live-set ^alt) dummy-name)
    (.add #^HashSet (:live-set ^alt) name)
    (loop [actions initial-plan
	   previous root]
      (if (empty? actions)
          (make-alt-plan-node node-type alt name previous)
	(recur (next actions)
	       (first (get-alt-node alt (first actions) previous))))))))

(defn alt-node [& args] (apply make-initial-alt-node args))



;; Graph stuff

(def *dummy-pair-alt* [Double/NEGATIVE_INFINITY (gensym)])

; Right now, subsumption only good for ignoring irrelevant predicates.
; Return true if keep, false if prune.
; Note, even strictly better subsumption checking can make things worse...

; Return true if keep, false if prune.
(defn graph-add-and-check! [alt node rest-plan name]
  (util/assert-is (:graph? alt))
  (let [#^HashMap graph-map (util/safe-get ^alt :graph-map)
	#^HashSet live-set  (util/safe-get ^alt :live-set)
	subsumption-info    (util/safe-get alt :subsumption-info)
	opt-val             (optimistic-valuation node)
	[opt-states opt-si] (get-valuation-states opt-val subsumption-info)
	graph-tuples        (.get graph-map [opt-states rest-plan])]
;   (println (count graph-tuples) (:graph? alt) (:class opt-val))
    (if-let [[_ _ bad-node]
	     (util/find-first
	   (fn [[graph-si graph-node]]
	     (not (or (and (= (:graph? alt) :icaps08) (not (.contains live-set graph-node)))
		      (not (valuation-subsumes? graph-si opt-si subsumption-info))
		      (and (not (= (:graph? alt) :sloppy))
		           (or (= (:graph? alt) :bhaskara) (not (.contains live-set graph-node)))
			   (valuation-equals? graph-si opt-si subsumption-info)))))
	   graph-tuples)]
        (do (util/sref-set! (:fate ^node) bad-node)
	    false)
     ; (println (class (get-valuation-states (pessimistic-valuation node) subsumption-info)))
      (let [pess-val              (pessimistic-valuation node)]
       ;(println " Survived" opt-si graph-tuples (map #(.contains live-set (second %)) graph-tuples))
	(when (> (valuation-max-reward pess-val) Double/NEGATIVE_INFINITY)
	  (let [[pess-states pess-si] (get-valuation-states pess-val subsumption-info)
		pair                  [pess-states rest-plan]
		graph-tuples          (.get graph-map pair)]
	    ;(println "cb " [pess-rew pess-states pess-si] graph-tuples)
;	    (println "cb " (count graph-tuples))
	    (when (every?
		   (fn [[graph-si graph-node]]
		     (or (not (valuation-subsumes? graph-si pess-si subsumption-info))
			 (and (not (.contains live-set graph-node)) ; Important that live subsumes dead.
			      (valuation-equals? graph-si pess-si subsumption-info))))
		   graph-tuples)
	      (.put graph-map pair
		(cons [pess-si name node] ;; TODO: remove node.
		      (remove
		       (fn [[graph-si graph-node]]
			 (valuation-subsumes? pess-si graph-si subsumption-info))
		       graph-tuples))))))
	true))))


	       

;; Node methods 

(defmethod search/reroot-at-node ::ALTPlanNode [node & args]
  (let [alt (:alt node)
	#^HashMap cache (:graph-map ^alt)
	#^HashSet live-set (:live-set ^alt)
	name   (util/safe-get node :name)]
    (.clear live-set)
    (.clear cache)
    (when (:graph? alt)
      (loop [node (:plan node), plan nil]
	(when node
	  (graph-add-and-check! alt node plan name)
	  (recur (:previous node) (cons (:hla node) plan)))))
    (.add live-set name)
;    (println "refs " (util/sref-get search/*ref-counter*))
;    (println (first args))
;    (println (:ref-choice-fn (:alt node)))
    (if (seq args)
        (assoc node :alt (assoc (:alt node) :ref-choice-fn (first args)))
      node)))
;  (.clear 



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
	  (valuation-max-reward (do-restrict-valuation-alt (pessimistic-valuation node) (:goal alt)))))))

(defmethod search/upper-reward-bound ::ALTPlanNode [node] 
  (let [alt (:alt node)
	node (:plan node)
	s (:upper-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
          (valuation-max-reward (do-restrict-valuation-alt (optimistic-valuation node) (:goal alt)))))))

(defmethod search/reward-so-far ::ALTPlanNode [node] 0)

(defmulti construct-immediate-refinement (fn [node previous actions alt name] (:class node)))
(defmethod construct-immediate-refinement ::ALTPlanNode [node previous actions alt name]
  (if (empty? actions) 
    (make-alt-plan-node (:class node) alt name previous )
    (let [[nxt cache?] (get-alt-node alt (first actions) previous)]
      (if (and (or (> (valuation-max-reward (optimistic-valuation nxt)) Double/NEGATIVE_INFINITY)
		   (and (util/sref-set! (:fate ^nxt) :dead) false))
	       (or (next actions) (not cache?)) ; Eliminate duplicates.
	       (or (not (:graph? alt)) 
		   (graph-add-and-check! alt nxt (next actions) name)))
	  (recur node nxt (next actions) alt name)
	(util/print-debug 3 "Late prune at" (search/node-str {:class ::ALTPlanNode :plan nxt})
			  (map println (map optimistic-valuation (util/iterate-while :previous nxt)))
;			  (optimistic-valuation (:previous (:previous nxt)))
			  )))))

(defmethod search/immediate-refinements ::ALTPlanNode [node] 
  (util/timeout)
  (util/sref-up! search/*ref-counter* inc)
  (let [urb         (search/upper-reward-bound node)
	alt         (util/safe-get node :alt)
	graph?      (util/safe-get alt :graph?)
	full-graph? (contains? #{:full :icaps08} graph?) ; (= graph? :full)
	plan        (:plan node)
	ref-node    ((util/safe-get alt :ref-choice-fn) node)]
    (when ref-node ;; If ref-fn is correct, == when not fully primitive
   ;   (println "About to refine " (search/node-str node) " at " (hla-name (:hla ref-node)))
      (let [after-actions  (map :hla (reverse (take-while #(not (identical? % ref-node)) 
							  (iterate :previous plan))))
	    before-nodes   (when full-graph? (reverse (util/iterate-while :previous plan)))
	    before-actions (map :hla (next before-nodes))
	    parent-name    (util/safe-get node :name)]
	(when graph? (.remove #^HashSet (:live-set ^alt) parent-name))
	(util/sref-set! (:fate ^ref-node) :refined)
	(filter identity
	 (for [ref (hla-immediate-refinements (:hla ref-node) (optimistic-valuation (:previous ref-node)))]
	   (let [name         ((:node-counter ^alt))
		 tail-actions (concat ref after-actions)
		 all-actions  (concat before-actions tail-actions)]
  	     (util/print-debug 3 "Considering refinement " (map hla-name ref) " at " (hla-name (:hla ref-node)))
	     (if (every? (fn [[node rest-plan]]    ; full graph prefix check
			     (graph-add-and-check! alt node rest-plan name))
			   (map vector before-nodes (iterate next all-actions)))
	       (when-let [nxt (construct-immediate-refinement node (:previous ref-node) tail-actions alt name )]
		 (when graph? (.add #^HashSet (:live-set ^alt) name))
;		 (when (> (search/upper-reward-bound nxt) urb) 
;		   (util/sref-set! (:upper-reward-bound ^(:plan nxt)) urb)
;		   (println "Fixing Upper Inconcistency" urb (search/upper-reward-bound nxt)))
		 nxt)
	       (util/print-debug 3 "early prune")
	       ))))))))


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

(defmethod search/node-first-action ::ALTPlanNode [node]
  (let [first-node (last (butlast (util/iterate-while :previous (:plan node))))
	first-hla  (:hla first-node)]
    (hla-primitive first-hla)))

(defmethod search/node-plan-length ::ALTPlanNode [node]
  (dec (count (util/iterate-while :previous (:plan node)))))

(defn alt-node-hla-count  [node]
  (count (remove #(hla-primitive? (:hla %)) (butlast (util/iterate-while :previous (:plan node))))))


;;; For ICAPS07 algorithm, and perhaps other uses

(defn state->condition [state instance]
  (let [all-atoms (util/to-set (util/safe-get (envs/get-state-space instance) :vars))]
    (envs/make-conjunctive-condition state (util/difference all-atoms state))))

(defn extract-state-seq [plan state-seq]
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
	state-seq (extract-state-seq (:plan node) [(first (valuation-max-reward-state
						    (restrict-valuation 
						     (pessimistic-valuation (:plan node))
						     (envs/get-goal env))))])
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


(require '[edu.berkeley.ai.util.graphviz :as graphviz])
(defn graphviz-alt [node]
  "TODO: identify source of node, etc."
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


(defn graphviz-alt2 [nodes]
  "TODO: identify source of node, etc."
  (doseq [node nodes,
	  n (util/iterate-while :previous (:plan node))]
    (assert (contains? #{nil :live} (util/sref-get (:fate ^n))))
    (util/sref-set! (:fate ^n) :live))
  (graphviz/write-graphviz "/tmp/alt.pdf"
   (last (util/iterate-while :previous (:plan (first nodes))))
   identity
   (fn [n] 
     (if (isa? (:class n) ::ALTPlanNode)
         {:label (util/double-quote [(search/lower-reward-bound n)
				     (search/upper-reward-bound n)])
	  :color "green"}
       (let [fate (util/sref-get (:fate ^n))]
	 {:label (util/double-quote [(valuation-max-reward (pessimistic-valuation n))
				     (valuation-max-reward (optimistic-valuation n))])
	  :color (cond 
		   (= :live fate) "green"
		   (and fate (not (= :refined fate))) "red" 
		   :else "black")})))
   (fn [n] 
     (when-not (isa? (:class n) ::ALTPlanNode)
     (let [parent-fate (util/sref-get (:fate ^n))]
       (cond (and parent-fate (not (= parent-fate :refined)) (not (= parent-fate :dead)) (not (= parent-fate :live)))
  	       (do (assert (empty? (:cache ^n)))
		   [[{:color "red" :style "dotted"} parent-fate]])
	     (and (= parent-fate :live) (empty? (:cache ^n)))
	       (let [final (util/make-safe (util/find-first #(identical? (:plan %) n) nodes))]
		 [[{:label (util/double-quote "[finish]") :color "green"} final]])
	     :else
	       (for [[e n] (:cache ^n)]
		 (let [fate (util/sref-get (:fate ^n))]
		   [{:label (util/double-quote (hla-name e)) 
		     :color (condp = fate :refined "blue" :live "green" "black")}  
		    n])))))))
  (doseq [node nodes,
	  n (util/iterate-while :previous (:plan node))]
    (util/sref-set! (:fate ^n) nil))
  (util/sh "open" "-a" "Skim" "/tmp/alt.pdf")
  )


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
   (doseq [simplifier [(second *simplifiers*)]
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