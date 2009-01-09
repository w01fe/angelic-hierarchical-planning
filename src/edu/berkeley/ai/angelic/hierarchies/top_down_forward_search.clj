(in-ns 'edu.berkeley.ai.angelic.hierarchies)


; According to contract, equality should be only on plan-tail and valuations if possible.  This is tree though.
; TODO: make hashing overhead optioanl in, e.g., LRTA*. (or not). 

(derive ::TopDownForwardNode :edu.berkeley.ai.search/Node)
(derive ::TopDownForwardRootNode ::TopDownForwardNode)

(defstruct top-down-forward-node  :class :goal :hla :previous)

(defn make-top-down-forward-node [env hla previous-node]
  (with-meta  
   (struct top-down-forward-node ::TopDownForwardNode (get-goal env) hla previous-node)
   {:pessimistic-valuation (sref nil), :optimistic-valuation (sref nil)}))



(defstruct top-down-forward-root-node :class :env :initial-valuation)

(defn make-top-down-forward-root-node [env initial-valuation]
  (struct top-down-forward-root-node ::TopDownForwardRootNode env initial-valuation))


(defn make-initial-top-down-forward-node [env initial-valuation initial-plan]
  (loop [actions initial-plan
	 previous (make-top-down-forward-root-node env initial-valuation)]
    (if (empty? actions)
        previous
      (recur (rest actions)
	     (make-top-down-forward-node env (first actions) previous)))))



(defmulti get-pessimistic-valuation :class)
(defmulti get-optimistic-valuation :class)

(defmethod get-pessimistic-valuation ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod get-optimistic-valuation  ::TopDownForwardRootNode [node] (:initial-valuation node))

(defmethod get-pessimistic-valuation ::TopDownForwardNode [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (sref-get s)
	(sref-set! s 
	  (progress-pessimistic 
	   (restrict-valuation (get-pessimistic-valuation (:previous node)) 
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-pessimistic-description (:hla node)))))))


(defmethod get-optimistic-valuation ::TopDownForwardNode [node]
  (let [s (:optimistic-valuation ^node)]
    (or (sref-get s)
	(sref-set! s 
	  (progress-optimistic 
	   (restrict-valuation (get-optimistic-valuation (:previous node))
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-optimistic-description (:hla node)))))))




(defmulti local-immediate-refinements (fn [node rest-actions] (:class node)))

(defmethod local-immediate-refinements ::TopDownForwardRootNode [node rest-actions]  nil)

; TODO: filter out dead ends here ???
(defmethod local-immediate-refinements ::TopDownForwardNode [node rest-actions]
  (when-not (hla-primitive (:hla node))
    (for [refinement (hla-immediate-refinements (:hla node) (get-optimistic-valuation node))]
      (loop [previous node,
	     actions (concat refinement rest-actions)]
	(if (empty? actions) 
	    previous
	  (recur 
	   (make-top-down-forward-node (:env node) (first actions) previous)
	   (rest actions)))))))


(defmethod dead-end?  ::TopDownForwardNode [node]
  (dead-end-valuation? (get-optimistic-valuation node)))

      

;;; Node methods 

(defmethod lower-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-lower-bound (restrict-valuation (get-pessimistic-valuation node) (:goal node))))

(defmethod upper-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-upper-bound (restrict-valuation (get-optimistic-valuation node) (:goal node))))

(defmethod reward-so-far ::TopDownForwardNode [node] 
  0) ;;TODO? 


(defmethod immediate-refinements ::TopDownForwardNode [node] 
  (concat-elts
   (loop [node node,
          rest-acts nil,
	  refinements nil]
     (if (= (:class node) ::TopDownForwardRootNode)
         refinements
       (recur (:previous node)
	      (cons (:hla node) rest-acts)
	      ;(delay-seq
	       (concat (local-immediate-refinements node rest-acts) refinements))))))


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
  (when-not (dead-end-valuation? (restrict-valuation (get-pessimistic-valuation node) (:goal (:env node))))
    (primitive-refinement node)))

(defmethod node-str ::TopDownForwardNode [node] 
  (apply str (map (comp hla-name :hla) (rest (rseq (iterate-while :previous node))))))


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
  )

;(defmethod node-parent ::TopDownForwardNode [node] 
;  Not implemented

;(defmethod node-depth ::TopDownForwardNode [node] 
;  (count (:act-seq ^(:state node))))

;(defmethod node-first-action ::TopDownForwardNode [node]
;  (nth (:act-seq ^(:state node)) 0))




