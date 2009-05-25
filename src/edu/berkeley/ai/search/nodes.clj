; Cast search in generic "refinement" setting. 
; Search space != state space, in general
; state-space search problems are a special case (of course)

(in-ns 'edu.berkeley.ai.search)

;;;;;;;;;;;;;;;;;; Interface for search nodes


(defmulti #^{:doc "Get the environment associated with this node"} node-environment :class)

(defmulti #^{:doc "A lower bound on the reward of the best refinement"} lower-reward-bound :class)

(defmulti #^{:doc "An upper bound on the reward of the best refinement"} upper-reward-bound :class)

(defmulti #^{:doc "Analogue of g-cost, if available"} reward-so-far :class)


(def *ref-counter* (util/sref 0))

(defn reset-ref-counter [] 
  (util/sref-set! *ref-counter* 0))

(defmulti #^{:doc "(pref. lazy) seq of node refinements; should begin with primitive.  Should increment ref-counter."} immediate-refinements :class)

(defmulti #^{:doc "If this node represents a single plan, return [it reward]; otherwise, return nil"} primitive-refinement :class)

(defmulti #^{:doc "Return [optimal-solution-element reward] in constant time, or return nil"} extract-optimal-solution :class)

(defmulti #^{:doc "Return any [solution-element reward] in constant time, or return nil.  Solution must have reward >= lower bound."} extract-a-solution :class)
(defmethod extract-a-solution ::Node [node] (extract-optimal-solution node))

(defmulti #^{:doc "Is this nodea provable dead-end?  Default implementation calls upper-reward-bound"} 
          dead-end? :class)
(defmethod dead-end? ::Node [node]
  (<= (upper-reward-bound node) Double/NEGATIVE_INFINITY))

(defmulti #^{:doc "[lower-bound upper-bound]"} reward-bounds :class)
(defmethod reward-bounds ::Node [node] 
  [(lower-reward-bound node) (upper-reward-bound node)])


(defmulti #^{:doc "Get a human-readable string version of this node"} node-str :class)
(defmethod node-str ::Node [node] 
  (str node))

(defmulti #^{:doc "Inform the data structure that all refinements but this one have been discarded, and return a new node."} reroot-at-node (fn [node & args] (:class node)))
(defmethod reroot-at-node ::Node [node] node)




;; Optional methods: may throw unsupportedoperationexception if desired.

(defmulti #^{:doc "Parent node"} node-parent :class)
(defmethod node-parent :Node [node] (throw (UnsupportedOperationException.)))

(defmulti #^{:doc "Depth of node"} node-depth :class)
(defmethod node-depth :Node [node] (throw (UnsupportedOperationException.)))

(defmulti #^{:doc "Length of plan at node"} node-plan-length :class)
(defmethod node-plan-length :Node [node] (throw (UnsupportedOperationException.)))

(defmulti #^{:doc "First primitive action at node"} node-first-action :class)
(defmethod node-first-action :Node [node] (throw (UnsupportedOperationException.)))

(defmulti #^{:doc "Env state associated with this node"} node-state :class)
(defmethod node-state :Node [node] (throw (UnsupportedOperationException.)))



;;; Some useful utility functions based on these definitions.

(defn node? [obj] 
  (and (map? obj) (isa? (:class obj) ::Node)))

(defn all-refinements- [pq priority-fn]
;  (print "\ntop")
  (when-not (queues/pq-empty? pq)
    (let [next (queues/pq-remove-min! pq)]
;      (print " " (first (:state next)) ": " )
      (if (dead-end? next) 
	  (recur pq priority-fn)
	(do
	  (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next)))
	  (lazy-seq (cons next (lazy-seq (all-refinements- pq priority-fn)))))))))

(defn all-refinements 
  "Returns a lazy seq of all refinements, refined using 
   the provided (presumed fresh) priority queue and priority function"
  [node pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (all-refinements- pq priority-fn))

(def *n nil)
(def *nn nil)
(def *ns nil)

(defn interactive-search 
  ([node] (interactive-search node (queues/make-tree-search-pq) #(- (upper-reward-bound %))))
  ([node pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (let [n-skip (util/sref 0)]
  (loop []
    (when-not (queues/pq-empty? pq)
      (let [[next p] (queues/pq-remove-min-with-cost! pq)
	    dead-end (dead-end? next)
	    sol      (extract-a-solution next)
	    refs (when-not (or dead-end sol) (immediate-refinements next))]
	(print "\n\n" (node-str next) p (reward-bounds next))
	(cond dead-end     (print " is a dead end.")
	      sol          (print " is a solution.")
	  :else (print " has refinements \n                    " 
                        (util/str-join "\n                     " (map #(str (reward-bounds %) " " 
									(node-str %)) refs)) "\n"))
	(or sol
	(when (or (when (> (util/sref-get n-skip) 0)
		    (util/sref-up! n-skip dec)
		    (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) refs))
		    true)
	       (loop []
		(print "\n(d)rop, (n)ext, (s)ave, (q)uit, (r)eroot, go (#), (expr ... *n/*nn/*ns)? ")
		(flush)
		(let [result (read)]
		  (cond (= result 'd) true
			(= result 'n) (do (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) refs)) true)
			(= result 'r) (do (while (not (queues/pq-empty? pq)) (queues/pq-remove-min! pq))
					  (queues/pq-add! pq next (priority-fn next))
					  true)
			(= result 's) (do (def *n next) (recur))
			(= result 'q) false
			(integer? result) (do (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) refs))
					      (util/sref-set! n-skip (dec result))
					      true)
;(dotimes [_ (dec result)]
;						(let [next (queues/pq-remove-min! pq)]
;						  (when-not (dead-end? next)
;						    (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next))))))
;					      true)
			:else          (do (print (binding [*n next *nn (first refs)
							    *ns (concat refs (map first (queues/pq-peek-pairs pq)))] 
						    (eval result)) "\n") (recur))))))
	  (recur)))))))))


(defn primitive-refinements 
  "Returns a lazy seq of primitive refinements, refined using 
   the provided (presumed fresh) priority queue and priority function"
  [node pq priority-fn]
  (filter primitive-refinement (all-refinements node pq priority-fn)))


(defn map-leaf-refinements- [f pq priority-fn]
  (when-not (queues/pq-empty? pq)
    (let [next (queues/pq-remove-min! pq)]
;      (when (f next) (prn next (f next)))
      (if (dead-end? next) 
	  (recur f pq priority-fn)
	(if-let [fnext (f next)]
	    (lazy-seq (cons fnext (map-leaf-refinements- f pq priority-fn)))
	  (do (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next)))
	      (recur f pq priority-fn)))))))

(defn leaf-refinements 
  "Returns a lazy seq of leaf refinements satisfying pred, refined using the provided 
   (presumed fresh) priority queue and priority function."
  [node pred pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (map-leaf-refinements- #(when (pred %) %) pq priority-fn))

(defn map-leaf-refinements 
  "Returns a lazy seq of true (f node) invocations, refined using the provided 
   (presumed fresh) priority queue and priority function."
  [node f pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (map-leaf-refinements- f pq priority-fn))

(defn refinements-depth
  "Returns a lazy seq of *mostly unique* refinement nodes at the desired depth (or optimal solns
   at lower depths, with search cutoff), computed by depth-first graph search, reopened if better.  
   node must support node-depth."
  [node f depth]
  (leaf-refinements 
   node 
   #(or (extract-optimal-solution %) (= (node-depth %) depth))
   (queues/make-graph-stack-pq) 
   #(- (upper-reward-bound %))))

(defn map-leaf-refinements-depth
  "A depth-limited version of map-leaf-refinements.  f is not applied to nodes with only depth or solution cutoffs."
  [node f depth]
  (map-leaf-refinements 
   node 
   #(or (f %)
	(and (or (extract-optimal-solution %) (= (node-depth %) depth)) %))
   (queues/make-graph-stack-pq) 
   #(- (upper-reward-bound %))))





;; These are somewhat misnomors, if hierarchy is infinite (e.g.) ?
; So far ignoring internal structure of nodes (bounds) 
(defn first-optimal-solution [node pq priority-fn]
  (some extract-optimal-solution
	(all-refinements node pq priority-fn)))


(defn first-solution [node pq priority-fn]
  (some extract-a-solution
	(all-refinements node pq priority-fn)))


(defn checked-algorithm [alg & args]
  (fn [node]
    (envs/check-solution (node-environment node)
      (apply alg node args))))

;;; A wrapper for nodes to change their cost bounds

(defstruct reward-adjusted-node :class :node :lower-reward :upper-reward)

(derive ::RewardAdjustedNode ::Node)

(defn adjust-reward 
  "A wrapper for nodes to change just their cost bounds.  No checking is done; be careful."
  ([node upper] (adjust-reward node (lower-reward-bound node) upper))
  ([node lower upper] (struct reward-adjusted-node ::RewardAdjustedNode node lower upper)))

(defmethod node-environment         ::RewardAdjustedNode [node] (node-environment         (:node node)))
(defmethod lower-reward-bound       ::RewardAdjustedNode [node] (:lower-reward node))
(defmethod upper-reward-bound       ::RewardAdjustedNode [node] (:upper-reward node))
(defmethod reward-so-far            ::RewardAdjustedNode [node] (reward-so-far            (:node node)))
(defmethod immediate-refinements    ::RewardAdjustedNode [node] (immediate-refinements    (:node node)))

;; Change these!
(defmethod primitive-refinement     ::RewardAdjustedNode [node] (throw (UnsupportedOperationException.))) 
       ; (primitive-refinement     (:node node)))
(defmethod extract-optimal-solution ::RewardAdjustedNode [node] (throw (UnsupportedOperationException.)))
       ; (extract-optimal-solution (:node node)))
(defmethod extract-a-solution       ::RewardAdjustedNode [node] (throw (UnsupportedOperationException.)))
       ; (extract-a-solution       (:node node)))

(defmethod dead-end?                ::RewardAdjustedNode [node] (dead-end?                (:node node)))
(defmethod node-parent              ::RewardAdjustedNode [node] (node-parent              (:node node)))
(defmethod node-depth               ::RewardAdjustedNode [node] (node-depth               (:node node)))
(defmethod node-first-action        ::RewardAdjustedNode [node] (node-first-action        (:node node)))
(defmethod node-state               ::RewardAdjustedNode [node] (node-state               (:node node)))
(defmethod node-str                 ::RewardAdjustedNode [node] 
  (str "<" (node-str (:node node)) " adjusted rew [" (:lower node) " " (:upper node) "]>"))

(defn reward-adjusted-node? [node] 
  (= (:class node) ::RewardAdjustedNode))

(defn ra-node-base [node]
  (util/assert-is (reward-adjusted-node? node))
  (:node node))

  











(comment 
  (map #(map :name (:act-seq ^(:state %)))
       (primitive-refinements-depth 
	(state-space-search-node  
	 (read-strips-planning-instance
	  (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")) 2)))




(comment 
(defn some-refinements- [pred pq priority-fn]
  (if (queues/pq-empty? pq) nil
    (let [next (queues/pq-remove-min! pq)]
      (if (pred next)
	(do (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next)))
    (lazy-seq (cons next (some-refinements- pred pq priority-fn))))
	(recur pred pq priority-fn)))))

(defn some-refinements 
  "Returns a lazy seq of refinements, refined using the provided (presumed fresh) 
   priority queue and priority function, cutting off branches where pred returns false."
  [node pred pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (some-refinements- pred pq priority-fn)))

(comment 
(defn iterate-refinements- [f pq priority-fn]
  (when-not (queues/pq-empty? pq)
    (let [next (f (queues/pq-remove-min! pq))]
      (lazy-seq (cons next
		 (do (when (node? next)
		       (queues/pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next))))
		     (iterate-refinements f pq priority-fn)))))))

(defn iterate-refinements 
  "Returns a lazy seq of (f refinement), refined using the provided (presumed fresh)
   priority queue and priority function.  When (f refinement) is a node, continues
   iteration; otherwise, stops. Filters out nil entries."
  [node f pq priority-fn]
  (queues/pq-add! pq node (priority-fn node))
  (iterate-refinements- f pq priority-fn)))