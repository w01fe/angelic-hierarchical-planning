(in-ns 'edu.berkeley.ai.angelic.hierarchies)

;;; Simple hierarchical search space, without any frills.
; Note: According to node contract, equality should be only on plan-tail and valuations if possible.  This is tree though, so forget that?

;; Nodes
; note that valuations are metadata so they aren't used in comparisons.

(derive ::TopDownForwardNode :edu.berkeley.ai.search/Node)
(defstruct top-down-forward-node  :class :goal :hla :previous)

(defn make-top-down-forward-node [goal hla previous-node]
  (with-meta  
   (struct top-down-forward-node ::TopDownForwardNode goal hla previous-node)
   {:pessimistic-valuation (sref nil), :optimistic-valuation (sref nil)}))


(derive ::TopDownForwardRootNode ::TopDownForwardNode)
(defstruct top-down-forward-root-node :class :goal :initial-valuation)

(defn make-top-down-forward-root-node [goal initial-valuation]
  (struct top-down-forward-root-node ::TopDownForwardRootNode goal initial-valuation))

(defn make-initial-top-down-forward-node [env initial-valuation initial-plan]
  (loop [actions initial-plan
	 previous (make-top-down-forward-root-node (get-goal env) initial-valuation)]
    (if (empty? actions)
        previous
      (recur (rest actions)
	     (make-top-down-forward-node (get-goal env) (first actions) previous)))))


;; Internal methods, used only in this file

(defmulti get-pessimistic-valuation :class)
(defmulti get-optimistic-valuation :class)
(defmulti local-immediate-refinements (fn [node rest-actions] (:class node)))

(defmethod get-pessimistic-valuation ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod get-optimistic-valuation  ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod local-immediate-refinements ::TopDownForwardRootNode [node rest-actions]  nil)

(defmethod get-pessimistic-valuation ::TopDownForwardNode [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (sref-get s)
	(sref-set! s 
	  (progress-pessimistic 
	   (restrict-valuation (get-pessimistic-valuation (:previous node)) 
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-pessimistic-description (:hla node)))))))


(defmethod get-optimistic-valuation ::TopDownForwardNode [node]
;  (prln (node-str node))
  (let [s (:optimistic-valuation ^node)]
    (or (sref-get s)
	(sref-set! s 
	  (progress-optimistic 
	   (restrict-valuation (get-optimistic-valuation (:previous node))
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-optimistic-description (:hla node)))))))


; TODO: filter out dead ends here ???
(defmethod local-immediate-refinements ::TopDownForwardNode [node rest-actions]
  (when-not (hla-primitive (:hla node))
    (for [refinement (hla-immediate-refinements (:hla node) (get-optimistic-valuation (:previous node)))]
      (loop [previous (:previous node),
	     actions (concat refinement rest-actions)]
	(if (empty? actions) 
	    previous
	  (recur 
	   (make-top-down-forward-node (:goal node) (first actions) previous)
	   (rest actions)))))))
      

;; Node methods 

(defmethod dead-end?  ::TopDownForwardNode [node]
  (dead-end-valuation? (get-optimistic-valuation node)))

(defmethod lower-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-lower-bound (restrict-valuation (get-pessimistic-valuation node) (:goal node))))

(defmethod upper-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-upper-bound (restrict-valuation (get-optimistic-valuation node) (:goal node))))

(defmethod reward-so-far ::TopDownForwardNode [node] 
  0) ;TODO? 

; TODO: add way to specify which HLA to refine.
(defmethod immediate-refinements ::TopDownForwardNode [node] 
  (let [nodes (rest (reverse (iterate-while :previous node)))]
    (when-let [rest-nodes (drop-while #(hla-primitive (:hla %)) nodes)]
      (local-immediate-refinements (first rest-nodes) (map :hla (rest rest-nodes))))))


(defmethod primitive-refinement ::TopDownForwardNode [node]
  (when-let [act-seq
	     (loop [act-seq '()
		    node node]
	       (if (= (:class node) ::TopDownForwardRootNode)
		   act-seq
		 (if-let [prim (hla-primitive (:hla node))]
		     (recur (cons prim act-seq) (:previous node))
		   false)))]
    (let [lower (lower-reward-bound node)
	  upper (upper-reward-bound node)]
      (assert-is (= lower upper))
      [act-seq lower])))

(defmethod extract-optimal-solution ::TopDownForwardNode [node] 
  (when-not (dead-end-valuation? (restrict-valuation (get-pessimistic-valuation node) (:goal node)))
    (primitive-refinement node)))

(defmethod node-str ::TopDownForwardNode [node] 
  (str-join " " (map (comp hla-name :hla) (rest (reverse (iterate-while :previous node))))))


;(defmethod node-parent ::TopDownForwardNode [node] 
;  Not implemented

;(defmethod node-depth ::TopDownForwardNode [node] 
;  (count (:act-seq ^(:state node))))

;(defmethod node-first-action ::TopDownForwardNode [node]
;  (nth (:act-seq ^(:state node)) 0))




(comment 
  (let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])] 
    (map :name (first (a-star-search 
    (make-initial-top-down-forward-node 
     env
     (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env)
     (list (instantiate-hierarchy
	    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env))) 
    ))))

(let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])
	val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env)
	    node
    (make-initial-top-down-forward-node 
     env
     val
     (list (instantiate-hierarchy
	    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env)))] 
        (map reward-bounds (immediate-refinements (first (immediate-refinements (first (immediate-refinements node)))))))

(let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])
	val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env)
	    node
    (make-initial-top-down-forward-node 
     env
     val
     (list (instantiate-hierarchy
	    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env)))] 
        (map #(vector (node-str %) (reward-bounds %)) (take 80 (all-refinements node (make-queue-pq) (constantly 0)))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env)))] (interactive-search node (make-queue-pq) (constantly 0)))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env)))] (a-star-search node))
  )




