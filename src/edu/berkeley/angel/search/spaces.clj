(in-ns 'edu.berkeley.angel.search)

; Cast search in generic "refinement" setting. 
; Search space != state space, in general
; state-space search problems are a special case (of course)

; refinement-fn returns a lazy seq of successor search states
; Equality for search states should be based on set of reachable states, 
; not set of reachable primitive plans or cost (more general) (???).

; ACTIONS are different from REFINEMENT STEPS
; Actions should have internal structure (name, fn, ... ?)
; Refinement steps need not, although it could be useful

; Goal should have potential to be structured too. 

; More specific -- search states are PlanSets ... methods:
;;  isEmpty?
;  dead-end?    
;  reward-so-far           -- analogue of g-cost, if applicable
;  lower-reward-bound
;  upper-reward-bound    -- should be consistent
;  reward-bounds
;  immediate-refinements
;  parent
;  depth
;  extract-a-solution       ; best-effort (nil if solution can't be found in constant time)
;  extract-optimal-solution ; best-effort (nil if solution can't be found in constant time)

; All these only work for countable spaces (where primitive refinements exist)
;  primitive-refinements-bfs
;  primitive-refinements-dfs
;  primitive-refinements-priority  
;  primitive-refinements-graph-bfs
;  primitive-refinements-graph-dfs
;  primitive-refinements-graph-priority  
  

; state should have act-seq, reward as meta.  

;; action-fn returns set of actions given state
;; action returns [result cost] pair


;(defstruct search-space :class :state-space :ref-fn)
;(defn make-search-space [ref-fn]
;  (struct search-space ::SearchSpace ref-fn))



(defmulti #^{:doc "A lower bound on the reward of the best refinement"} lower-reward-bound :class)
(defmulti #^{:doc "An upper bound on the reward of the best refinement"} upper-reward-bound :class)
(defmulti #^{:doc "Analogue of g-cost, if available"} reward-so-far :class)
(defmulti #^{:doc "(pref. lazy) seq of search-state refinements; should begin with primitive."} immediate-refinements :class)
(defmulti #^{:doc "If this state represents a single plan, return [it reward]; otherwise, return nil"} primitive-refinement :class)
(defmulti #^{:doc "Return [optimal solution element reward] in constant time, or return nil"} extract-optimal-solution :class)


(defmulti #^{:doc "Return any [solution element reward] in constant time, or return nil"} extract-a-solution :class)
(defmethod extract-a-solution ::SearchState [search-state] (extract-optimal-solution search-state))

(defmulti #^{:doc "Is this search state a provable dead-end?  Default implementation calls lower-reward-bound"} 
          dead-end? :class)
(defmethod dead-end? ::SearchState [search-state]
  (<= (upper-reward-bound search-state) Double/NEGATIVE_INFINITY))

(defmulti #^{:doc "[lower-bound upper-bound]"} reward-bounds :class)
(defmethod reward-bounds ::SearchState [search-state] 
  [(lower-reward-bound search-state) (upper-reward-bound search-state)])

;(defmulti #^{:doc "Parent search-state"} parent :class)
;(defmulti #^{:doc "Depth of search-state"} parent :class)

(defn all-refinements- [pq priority-fn]
;  (print "\ntop")
  (if (pq-empty? pq) nil
    (let [next (pq-remove-min! pq)]
;      (print " " (first (:state next)) ": " )
      (pq-add-all! pq (map (fn [i] [i (priority-fn i)]) (immediate-refinements next)))
      (lazy-cons next (all-refinements- pq priority-fn)))))
  
(defn all-refinements "Returns a lazy seq of all refinements, refined using 
                       the provided (presumed fresh) priority queue and priority function"
  [search-state pq priority-fn]
  (pq-add! pq search-state (priority-fn search-state))
  (all-refinements- pq priority-fn))

(defn primitive-refinements "Returns a lazy seq of primitive refinements, refined using 
                             the provided (presumed fresh) priority queue and priority function"
  [search-state pq priority-fn]
  (filter primitive-refinement (all-refinements search-state pq priority-fn)))


;; TODO: these are somewhat misnomors, if hierarchy is infinite (e.g.)
; So far ignoring internal structure of search-state nodes (bounds, extract-a-sol, ...) 
(defn first-optimal-solution [search-state pq priority-fn]
  (some extract-optimal-solution
	(all-refinements search-state pq priority-fn)))


(defn first-solution [search-state pq priority-fn]
  (some extract-a-solution
	(all-refinements search-state pq priority-fn)))





; A state space for standard forward search, 
(derive ::StateSpaceSearchSpace ::SearchSpace)
(defstruct state-space-search-space :class :action-space :goal :lower-reward-fn :upper-reward-fn)
(defn- make-state-space-search-space [action-space goal lower-reward-fn upper-reward-fn]
  (struct state-space-search-space ::StateSpaceSearchSpace action-space goal lower-reward-fn upper-reward-fn))

(derive ::StateSpaceSearchState ::SearchState)
(defstruct state-space-search-state :class :search-space :state)
(defn- make-state-space-search-state [search-space state]
  (struct state-space-search-state ::StateSpaceSearchState search-space state))

(derive ::StateSpaceSearchStateLeaf ::StateSpaceSearchState)
(defstruct state-space-search-state-leaf :class :search-space :state)
(defn- make-state-space-search-state-leaf [search-space state]
  (struct state-space-search-state-leaf ::StateSpaceSearchStateLeaf search-space state))


(defn search-problem->state-space-search-state [problem lower-reward-fn upper-reward-fn]
  (make-state-space-search-state 
   (make-state-space-search-space (get-action-space problem) (get-goal problem) lower-reward-fn upper-reward-fn)
   (get-initial-state problem)))


(defmethod lower-reward-bound ::StateSpaceSearchState [search-state] 
  (+ (:reward ^(:state search-state)) ((:lower-reward-fn (:search-space search-state)) (:state search-state))))

(defmethod upper-reward-bound ::StateSpaceSearchState [search-state] 
  (+ (:reward ^(:state search-state)) ((:upper-reward-fn (:search-space search-state)) (:state search-state))))

(defmethod reward-so-far ::StateSpaceSearchState [search-state] 
  (:reward ^(:state search-state)))

(defmethod immediate-refinements ::StateSpaceSearchState [search-state] 
  (let [search-space (:search-space search-state)
	state (:state search-state)]
    (lazy-cons (make-state-space-search-state-leaf search-space state)
	       (map #(make-state-space-search-state search-space %) 
		    (successor-states state (:action-space search-space))))))

 

(defmethod primitive-refinement ::StateSpaceSearchState [search-state] 
  nil)

(defmethod extract-optimal-solution ::StateSpaceSearchState [search-state] 
  nil)



(defmethod immediate-refinements ::StateSpaceSearchStateLeaf [search-state] nil)
;  (throw (UnsupportedOperationException. "Primitive refinements don't have immediate refs.")))

(defmethod primitive-refinement ::StateSpaceSearchStateLeaf [search-state] 
  [(:act-seq ^(:state search-state)) (:reward ^(:state search-state))])

(defmethod extract-optimal-solution ::StateSpaceSearchStateLeaf [search-state] 
  (when (satisfies-goal? (:state search-state) (:goal (:search-space search-state)))
    (primitive-refinement search-state)))




(comment
(take 5 (distinct (primitive-refinements-priority 
(search-problem->state-space-search-state
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

(defn successors [state action-fn]
  "Return a lazy seq of (action successor cost) seqs"
  (map #(cons (:name %) (apply-action state %)) (action-fn state)))

(defn successor-states [state action-fn]
  "Return a lazy seq of successor states"
  (map #(first (apply-action state %)) (action-fn state)))
 
(defstruct search-space :class :state-space :action-space :action-fn)

(defn make-search-space [state-space action-space action-fn]
  (struct search-space ::SearchSpace state-space action-space action-fn))


(defstruct search-problem :class :search-space :initial-state :goal-test)

(defn make-search-problem [search-space initial-state goal-test]
  (struct search-problem ::SearchProblem search-space initial-state goal-test))

(defn successors [state action-fn]
  "Return a lazy seq of (action successor cost) seqs"
  (map #(cons (:name %) (apply-action state %)) (action-fn state)))

(defn successor-states [state action-fn]
  "Return a lazy seq of successor states"
  (map #(first (apply-action state %)) (action-fn state)))


)