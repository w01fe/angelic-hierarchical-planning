(in-ns 'edu.berkeley.ai.angelic.hierarchies)


; According to contract, equality should be only on plan-tail and valuations if possible.  This is tree though.
; TODO: make hashing overhead optioanl in, e.g., LRTA*. (or not). 

(derive ::TopDownForwardNode ::Node)
(derive ::TopDownForwardRootNode ::TopDownForwardNode)

(defstruct top-down-forward-node      :class :search-space :hla :previous)

(defn make-top-down-forward-node [search-space hla previous-node]
  (with-meta  
   (struct top-down-forward-node ::TopDownForwardNode search-space hla previous-node)
   {:pessimistic-valuation (sref nil), :optimistic-valuation (sref nil)}))



(defstruct top-down-forward-root-node :class :search-space :initial-valuation)

(defn make-top-down-forward-root-node [search-space initial-valuation]
  (struct top-down-forward-root-node ::TopDownForwardRootNode search-space initial-valuation))


(defn make-initial-top-down-forward-node [search-space initial-valuation initial-plan]
  (loop [actions initial-plan
	 previous (make-top-down-forward-root-node search-space initial-valuation)]
    (if (empty? actions)
        previous
      (recur (rest actions)
	     (make-top-down-forward-node search-space (first actions) previous)))))



(defmulti local-immediate-refinements (fn [node rest-actions] (:class node)))

(defmethod local-immediate-refinements ::TopDownForwardRootNode [node rest-actions]  nil)

(defmethod local-immediate-refinements ::TopDownForwardNode [node rest-actions]
  (when-not (hla-primitive (:hla node))
    (for [refinement (hla-immediate-refinements (:hla node))]
      (loop [previous node,
	     actions (concat refinement rest-actions)]
	(if (empty? actions) 
	    previous
	  (recur 
	   (make-top-down-forward-node (:search-space node) (first actions) previous)
	   (rest actions)))))))




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



      

;;; Node methods 

(defmethod lower-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-lower-bound (restrict-valuation (get-pessimistic-valuation node) (:goal (:search-space node)))))

(defmethod upper-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-upper-bound (restrict-valuation (get-optimistic-valuation node) (:goal (:search-space node)))))

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
  (when-not (dead-end? (restrict-valuation (get-pessimistic-valuation node) (:goal (:search-space node))))
    (primitive-refinement node)))

(defmethod node-str ::TopDownForwardNode [node] 
  (apply str (map (comp hla-name :hla) (rest (rseq (iterate-while :previous node))))))




;(defmethod node-parent ::TopDownForwardNode [node] 
;  Not implemented

;(defmethod node-depth ::TopDownForwardNode [node] 
;  (count (:act-seq ^(:state node))))

;(defmethod node-first-action ::TopDownForwardNode [node]
;  (nth (:act-seq ^(:state node)) 0))




