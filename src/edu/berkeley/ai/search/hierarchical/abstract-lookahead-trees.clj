(in-ns 'edu.berkeley.ai.search.hierarchical)
(comment 
(derive ::AltNode ::Node)

; TODO: use forward hashmaps in metadata for children?

(defstruct hierarchical-search-space-struct :class :state-space :action-space :goal :top-level-action)

(defn make-hierarchical-search-space- [state-space action-space goal top-level-action ]
  (struct state-space-search-space-struct ::HierarchicalSearchSpace state-space action-space goal top-level-action ))


; According to contract, equality should be only on plan-tail and valuations if possible.  This is tree though.
; TODO: make hashing overhead optioanl in, e.g., LRTA*. 

(derive ::RootNode   ::ALTNode)
(derive ::ActionNode ::ALTNode)
(derive ::ActionNode ::Node)

(defstruct root-node :class :search-space )

(defstruct alt-node :class :search-space :plan)

(defn make-alt-node [search-space state]
  (struct alt-node ::ALTNode search-space state))



(defmethod immediate-refinements nil [act-seq position]
  (map #(plug act-seq count %) act-seq))

(defmethod immediate-refinements nil [act-seq]
  (concat-elts
   (for [position (range (count act-seq))]
     (immediate-refinements act-seq position))))






;;; Main node data structure




;;; Only methods to call here is:

(defn alt-search-space
  ([env] 
     (alt-search-space env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (alt-search-space env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
  ([env lower-reward-fn upper-reward-fn]
     (make-alt-search-space- (get-alt env) (get-action-space env) (get-goal env) lower-reward-fn upper-reward-fn)))

(defn alt-search-node 
  ([env] 
     (alt-search-node env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (alt-search-node env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
  ([env lower-reward-fn upper-reward-fn]
     (make-alt-node 
      (make-alt-search-space- (get-alt node) (get-action-space env) (get-goal env) lower-reward-fn upper-reward-fn)
      (get-initial-state env))))  

;;; Node methods 

(defmethod lower-reward-bound ::ALTNode [node] 
  (+ (:reward ^(:state node)) ((:lower-reward-fn (:search-space node)) (:state node))))

(defmethod upper-reward-bound ::ALTNode [node] 
  (+ (:reward ^(:state node)) ((:upper-reward-fn (:search-space node)) (:state node))))

(defmethod reward-so-far ::ALTNode [node] 
  (:reward ^(:state node)))

(defmethod immediate-refinements ::ALTNode [node] 
  (let [search-space (:search-space node)
	state (:state node)]
    (map #(make-alt-node search-space %) 
	 (successor-states state (:action-space search-space)))))

(defmethod primitive-refinement ::ALTNode [node] 
  nil)

(defmethod extract-optimal-solution ::ALTNode [node] 
  (and (= (upper-reward-bound node)
	  (reward-so-far node))
       (extract-a-solution node)))

(defmethod extract-a-solution ::ALTNode [node]
  (when (satisfies-goal? (:state node) (:goal (:search-space node)))
    [(:act-seq ^(:state node)) (:reward ^(:state node))]))

(defmethod node-str ::ALTNode [node] 
  (state-str (:alt (:search-space node)) (:state node)))


;(defmethod node-parent ::ALTNode [node] 
;  Not implemented

(defmethod node-depth ::ALTNode [node] 
  (count (:act-seq ^(:state node))))

(defmethod node-first-action ::ALTNode [node]
  (nth (:act-seq ^(:state node)) 0))



)
