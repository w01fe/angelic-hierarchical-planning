; A node implementation for forward state-space search on an deterministic, FO, countable environment with finite action space.
; Two versions are possible: produce primitive refinements or not.  
;   Now, this version does not.  Old version that does is below.
;   (if you want that, use flat hierarchy?)

(in-ns 'edu.berkeley.ai.search)


;;; An auxillary data structure to hold cached features of env, heuristics.

(defstruct state-space-search-space-struct :class :state-space :action-space :goal :lower-reward-fn :upper-reward-fn)

(defn make-state-space-search-space- [state-space action-space goal lower-reward-fn upper-reward-fn]
  (struct state-space-search-space-struct ::StateSpaceSearchSpace state-space action-space goal lower-reward-fn upper-reward-fn))


;;; Main node data structure

(derive ::StateSpaceNode ::Node)

(defstruct state-space-node :class :search-space :state)

(defn make-state-space-node [search-space state]
  (struct state-space-node ::StateSpaceNode search-space state))


;;; Only methods to call here is:

(defn state-space-search-space
  ([env] 
     (state-space-search-space env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (state-space-search-space env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
  ([env lower-reward-fn upper-reward-fn]
     (make-state-space-search-space- (get-state-space env) (get-action-space env) (get-goal env) lower-reward-fn upper-reward-fn)))

(defn state-space-search-node 
  ([env] 
     (state-space-search-node env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (state-space-search-node env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
  ([env lower-reward-fn upper-reward-fn]
     (make-state-space-node 
      (make-state-space-search-space- (get-state-space env) (get-action-space env) (get-goal env) lower-reward-fn upper-reward-fn)
      (get-initial-state env))))  

;;; Node methods 

(defmethod lower-reward-bound ::StateSpaceNode [node] 
  (+ (:reward ^(:state node)) ((:lower-reward-fn (:search-space node)) (:state node))))

(defmethod upper-reward-bound ::StateSpaceNode [node] 
  (+ (:reward ^(:state node)) ((:upper-reward-fn (:search-space node)) (:state node))))

(defmethod reward-so-far ::StateSpaceNode [node] 
  (:reward ^(:state node)))

(defmethod immediate-refinements ::StateSpaceNode [node] 
  (let [search-space (:search-space node)
	state (:state node)]
    (map #(make-state-space-node search-space %) 
	 (successor-states state (:action-space search-space)))))

(defmethod primitive-refinement ::StateSpaceNode [node] 
  nil)

(defmethod extract-optimal-solution ::StateSpaceNode [node] 
  (and (= (upper-reward-bound node)
	  (reward-so-far node))
       (extract-a-solution node)))

(defmethod extract-a-solution ::StateSpaceNode [node]
  (when (satisfies-goal? (:state node) (:goal (:search-space node)))
    [(:act-seq ^(:state node)) (:reward ^(:state node))]))

(defmethod node-str ::StateSpaceNode [node] 
  (state-str (:state-space (:search-space node)) (:state node)))


;(defmethod node-parent ::StateSpaceNode [node] 
;  Not implemented

(defmethod node-depth ::StateSpaceNode [node] 
  (count (:act-seq ^(:state node))))

(defmethod node-first-action ::StateSpaceNode [node]
  (nth (:act-seq ^(:state node)) 0))




(comment
(take 5 (distinct (primitive-refinements-priority 
(search-problem->state-space-node
  (make-search-problem 
   (list 5)
   (let [act-inc (make-action 'inc #(vector (list (inc (first %))) -1))
	 act-dec (make-action 'dec #(vector (list (dec (first %))) -1))] 
     (make-action-space 
      (fn [state]
	(cond (= (first state) 10) [act-dec]
	      (= (first state) 0)  [act-inc]
	      true                 [act-inc act-dec]))))
   (make-goal #(zero? (first %))))
  (constantly Double/NEGATIVE_INFINITY)
  (constantly 0)))))
   ) 










(comment 

;;; An auxillary data structure to hold cached features of env, heuristics.

(defstruct state-space-search-space :class :action-space :goal :lower-reward-fn :upper-reward-fn)

(defn- make-state-space-search-space [action-space goal lower-reward-fn upper-reward-fn]
  (struct state-space-search-space ::StateSpaceSearchProblem action-space goal lower-reward-fn upper-reward-fn))


;;; Main node data structure; non-primitive and primitive nodes

(derive ::StateSpaceNode ::Node)

(defstruct state-space-node :class :search-space :state)

(defn- make-state-space-node [search-space state]
  (struct state-space-node ::StateSpaceNode search-space state))


(derive ::StateSpaceNodeLeaf ::StateSpaceNode)

(defstruct state-space-node-leaf :class :search-space :state)

(defn- make-state-space-node-leaf [search-space state]
  (struct state-space-node-leaf ::StateSpaceNodeLeaf search-space state))


;;; Only method to call here is:

(defn state-space-search-node 
  ([env] 
     (state-space-search-node env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (state-space-search-node env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
  ([env lower-reward-fn upper-reward-fn]
     (make-state-space-node 
      (make-state-space-search-space (get-action-space env) (get-goal env) lower-reward-fn upper-reward-fn)
      (get-initial-state env))))
  

;;; Node methods for (non-)leaves

(defmethod lower-reward-bound ::StateSpaceNode [node] 
  (+ (:reward ^(:state node)) ((:lower-reward-fn (:search-space node)) (:state node))))

(defmethod upper-reward-bound ::StateSpaceNode [node] 
  (+ (:reward ^(:state node)) ((:upper-reward-fn (:search-space node)) (:state node))))

(defmethod reward-so-far ::StateSpaceNode [node] 
  (:reward ^(:state node)))

(defmethod immediate-refinements ::StateSpaceNode [node] 
  (let [search-space (:search-space node)
	state (:state node)]
    (lazy-cons (make-state-space-node-leaf search-space state)
	       (map #(make-state-space-node search-space %) 
		    (successor-states state (:action-space search-space))))))

(defmethod primitive-refinement ::StateSpaceNode [node] 
  nil)

(defmethod extract-optimal-solution ::StateSpaceNode [node] 
  nil)

;(defmethod node-parent ::StateSpaceNode [node] 
;  Not implemented

(defmethod node-depth ::StateSpaceNode [node] 
  (count (:act-seq ^(:state node))))


;;; Methods for leaves 

(defmethod immediate-refinements ::StateSpaceNodeLeaf [node] nil)
;  (throw (UnsupportedOperationException. "Primitive refinements don't have immediate refs.")))

(defmethod primitive-refinement ::StateSpaceNodeLeaf [node] 
  [(:act-seq ^(:state node)) (:reward ^(:state node))])

(defmethod extract-optimal-solution ::StateSpaceNodeLeaf [node] 
  (when (satisfies-goal? (:state node) (:goal (:search-space node)))
    (primitive-refinement node)))




(comment
(take 5 (distinct (primitive-refinements-priority 
(search-problem->state-space-node
  (make-search-problem 
   (list 5)
   (let [act-inc (make-action 'inc #(vector (list (inc (first %))) -1))
	 act-dec (make-action 'dec #(vector (list (dec (first %))) -1))] 
     (make-action-space 
      (fn [state]
	(cond (= (first state) 10) [act-dec]
	      (= (first state) 0)  [act-inc]
	      true                 [act-inc act-dec]))))
   (make-goal #(zero? (first %))))
  (constantly Double/NEGATIVE_INFINITY)
  (constantly 0)))))
   ) 


)





