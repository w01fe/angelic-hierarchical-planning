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
   {:pessimistic-valuation (util/sref nil), :optimistic-valuation (util/sref nil)}))


(derive ::TopDownForwardRootNode ::TopDownForwardNode)
(defstruct top-down-forward-root-node :class :goal :initial-valuation)

(defn make-top-down-forward-root-node [goal initial-valuation]
  (struct top-down-forward-root-node ::TopDownForwardRootNode goal initial-valuation))

(defn make-initial-top-down-forward-node [env initial-valuation initial-plan]
  (loop [actions initial-plan
	 previous (make-top-down-forward-root-node (envs/get-goal env) initial-valuation)]
    (if (empty? actions)
        previous
      (recur (rest actions)
	     (make-top-down-forward-node (envs/get-goal env) (first actions) previous)))))


;; Internal methods, used only in this file

(defmulti get-pessimistic-valuation :class)
(defmulti get-optimistic-valuation :class)
(defmulti local-immediate-refinements (fn [node rest-actions] (:class node)))

(defmethod get-pessimistic-valuation ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod get-optimistic-valuation  ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod local-immediate-refinements ::TopDownForwardRootNode [node rest-actions]  nil)

(defmethod get-pessimistic-valuation ::TopDownForwardNode [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-pessimistic 
	   (restrict-valuation (get-pessimistic-valuation (:previous node)) 
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-pessimistic-description (:hla node)))))))


(defmethod get-optimistic-valuation ::TopDownForwardNode [node]
;  (util/prln (search/node-str node))
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
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

(defmethod search/dead-end?  ::TopDownForwardNode [node]
  (empty-valuation? (get-optimistic-valuation node)))

(defmethod search/lower-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-lower-bound (restrict-valuation (get-pessimistic-valuation node) (:goal node))))

(defmethod search/upper-reward-bound ::TopDownForwardNode [node] 
  (get-valuation-upper-bound (restrict-valuation (get-optimistic-valuation node) (:goal node))))

(defmethod search/reward-so-far ::TopDownForwardNode [node] 
  0) ;TODO? 


(def *ref-counter* (make-array Integer/TYPE 1))

(defn reset-ref-counter [] 
  (aset *ref-counter* 0 0))

; TODO: add way to specify which HLA to refine.
(defmethod search/immediate-refinements ::TopDownForwardNode [node] 
  (aset *ref-counter* 0 (inc (aget *ref-counter* 0)))
  (let [nodes (rest (reverse (util/iterate-while :previous node)))]
    (when-let [rest-nodes (drop-while #(hla-primitive (:hla %)) nodes)]
      (local-immediate-refinements (first rest-nodes) (map :hla (rest rest-nodes))))))


(defmethod search/primitive-refinement ::TopDownForwardNode [node]
  (when-let [act-seq
	     (loop [act-seq '()
		    node node]
	       (if (= (:class node) ::TopDownForwardRootNode)
		   act-seq
		 (if-let [prim (hla-primitive (:hla node))]
		     (recur (cons prim act-seq) (:previous node))
		   false)))]
    (let [lower (search/lower-reward-bound node)
	  upper (search/upper-reward-bound node)]
      (util/assert-is (= lower upper))
      [act-seq lower])))

(defmethod search/extract-optimal-solution ::TopDownForwardNode [node] 
  (when-not (empty-valuation? (restrict-valuation (get-pessimistic-valuation node) (:goal node)))
    (search/primitive-refinement node)))

(defmethod search/node-str ::TopDownForwardNode [node] 
  (util/str-join " " (map (comp hla-name :hla) (rest (reverse (util/iterate-while :previous node))))))


;(defmethod search/node-parent ::TopDownForwardNode [node] 
;  Not implemented

;(defmethod search/node-depth ::TopDownForwardNode [node] 
;  (count (:act-seq ^(:state node))))

;(defmethod search/node-first-action ::TopDownForwardNode [node]
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
        (map #(vector (search/node-str %) (reward-bounds %)) (take 80 (all-refinements node (make-queue-pq) (constantly 0)))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env)))] (interactive-search node (make-queue-pq) (constantly 0)))

(u util envs search search.algorithms.textbook angelic angelic.hierarchies domains.nav-switch domains.strips)

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env)))] (check-solution env (a-star-search node)))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 35 35 [[1 1]] [34 0] true [0 34]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env)))] (time (second (a-star-search node))))

; Flat hierarchies
(let [env (make-nav-switch-env 6 6 [[1 1]] [5 0] true [0 5]), val (make-initial-valuation :edu.berkeley.ai.angelic/ExplicitValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 4))))) ) env)))] (time (second (a-star-search node))))

(let [env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]), val (make-initial-valuation :edu.berkeley.ai.angelic/ExplicitValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env)))] (time (second (a-star-search node))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]), val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation env), node (make-initial-top-down-forward-node env val (list (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (fn [state] (* -2 (+ (Math/abs (- (desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env)))] (time (second (a-star-search node))))

  )


(comment 
 ; Speed analysis, 6x6 nav-switch, no heuristic
 ; explicit domain, no hierarchy  : 3.5 s
 ; strips   domain, no hierarchy  : 3.5 s
 ; explicit domain, flat hierarchy: 14.6 s
 ; strips   domain, flat hierarchy: 17.5
 ; strips domain, strips flat hier: 201 s
 ; -- long way to go 


 )

