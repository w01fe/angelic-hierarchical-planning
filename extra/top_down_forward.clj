(in-ns 'edu.berkeley.ai.angelic.hierarchies)

;;; Simple hierarchical search space, without any frills.
; Note: According to node contract, equality should be only on plan-tail and valuations if possible.  This is tree though, so forget that?

;; Nodes
; note that valuations are metadata so they aren't used in comparisons.

(defn first-nonprimitive [node]
  (let [np (:first-np node)]
    (cond (true? np) node
	  np np)))

(derive ::TopDownForwardNode :edu.berkeley.ai.search/Node)
(defstruct top-down-forward-node  :class :goal :hla :previous :first-np)

(defn make-top-down-forward-node [goal hla previous-node]
  (with-meta  
   (struct top-down-forward-node ::TopDownForwardNode goal hla previous-node 
	   (or (first-nonprimitive previous-node) (and (not (hla-primitive? hla)) true)))
   {:pessimistic-valuation (util/sref nil), :optimistic-valuation (util/sref nil)
    :lower-reward-bound (util/sref nil) :upper-reward-bound (util/sref nil)
    }))


(derive ::TopDownForwardRootNode ::TopDownForwardNode)
(defstruct top-down-forward-root-node :class :goal :initial-valuation :first-np)

(defn make-top-down-forward-root-node [goal initial-valuation]
  (struct top-down-forward-root-node ::TopDownForwardRootNode goal initial-valuation nil))

(defn make-initial-top-down-forward-node 
  ([initial-node] (make-initial-top-down-forward-node 
		   (hla-default-valuation-type initial-node)
		   initial-node))
  ([valuation-class initial-node]
  (let [env (hla-environment initial-node)]
    (loop [actions (list initial-node)
	   previous (make-top-down-forward-root-node 
		     (envs/get-goal env) 
		     (make-initial-valuation valuation-class env))]
      (if (empty? actions)
        previous
	(recur (next actions)
	       (make-top-down-forward-node (envs/get-goal env) (first actions) previous)))))))

(defn tdf-node 
  ([initial-hla] (make-initial-top-down-forward-node initial-hla))
  ([val-class initial-hla] (make-initial-top-down-forward-node val-class initial-hla)))

;; Internal methods, used only in this file

(defmulti get-pessimistic-valuation :class)
(defmulti get-optimistic-valuation :class)
(defmulti local-immediate-refinements (fn [node rest-actions] (:class node)))

(defmethod get-pessimistic-valuation ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod get-optimistic-valuation  ::TopDownForwardRootNode [node] (:initial-valuation node))
(defmethod local-immediate-refinements ::TopDownForwardRootNode [node rest-actions]  nil)

(defn do-restrict-valuation [x y]
  (restrict-valuation x y))

(defmethod get-pessimistic-valuation ::TopDownForwardNode [node]
  (let [s (:pessimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-pessimistic 
	   (do-restrict-valuation (get-pessimistic-valuation (:previous node)) 
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-pessimistic-description (:hla node)))))))


(defmethod get-optimistic-valuation ::TopDownForwardNode [node]
;  (util/prln (search/node-str node))
  (let [s (:optimistic-valuation ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (progress-optimistic 
	   (do-restrict-valuation (get-optimistic-valuation (:previous node))
			       (hla-hierarchical-preconditions (:hla node)))
	   (hla-optimistic-description (:hla node)))))))


; TODO: filter out dead ends here ???
(defmethod local-immediate-refinements ::TopDownForwardNode [node rest-actions]
  (when-not (hla-primitive? (:hla node))
    (for [refinement (hla-immediate-refinements (:hla node) (get-optimistic-valuation (:previous node)))]
      (loop [previous (:previous node),
	     actions (concat refinement rest-actions)]
	(if (empty? actions) 
	    previous
	  (recur 
	   (make-top-down-forward-node (:goal node) (first actions) previous)
	   (next actions)))))))
      

;; Node methods 

; Don't want this, doesn't take goal into account!
;(defmethod search/dead-end?  ::TopDownForwardNode [node]
;  (empty-valuation? (get-optimistic-valuation node)))

(defmethod search/node-environment   ::TopDownForwardRootNode [node] (throw (IllegalArgumentException.)))
(defmethod search/node-environment   ::TopDownForwardNode [node] (hla-environment (:hla node)))

(defmethod search/node-state   ::TopDownForwardNode [node]
  (if (= (:class (:previous node)) ::TopDownForwardRootNode)
      (envs/get-initial-state (hla-environment (:hla node)))
    (throw (IllegalArgumentException.))))


(defmethod search/lower-reward-bound ::TopDownForwardRootNode [node] 
  (get-valuation-lower-bound (do-restrict-valuation (get-pessimistic-valuation node) (:goal node))))

(defmethod search/upper-reward-bound ::TopDownForwardRootNode [node] 
  (get-valuation-upper-bound (do-restrict-valuation (get-optimistic-valuation node) (:goal node))))

(defmethod search/lower-reward-bound ::TopDownForwardNode [node] 
;  (prn "lb")
  (let [s (:lower-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
	  (get-valuation-lower-bound (do-restrict-valuation (get-pessimistic-valuation node) (:goal node)))))))


(defmethod search/upper-reward-bound ::TopDownForwardNode [node] 
;  (prn "ub")
  (let [s (:upper-reward-bound ^node)]
    (or (util/sref-get s)
	(util/sref-set! s 
          (get-valuation-upper-bound (do-restrict-valuation (get-optimistic-valuation node) (:goal node)))))))


(defmethod search/reward-so-far ::TopDownForwardNode [node] 
;  (prn "sf")
  0) ;TODO? 



; Note: what follows assumes that descriptions for primitives are exact.

; TODO: add way to specify which HLA to refine.
(defmethod search/immediate-refinements ::TopDownForwardNode [node] 
  (util/timeout)
  (util/sref-set! *ref-counter* (inc (util/sref-get *ref-counter*)))
  (when-let [fnp (first-nonprimitive node)]
    (local-immediate-refinements fnp (reverse (map :hla (take-while #(not (identical? % fnp)) (iterate :previous node))))))) 
;  (let [nodes (next (reverse (util/iterate-while :previous node)))]
;    (when-let [rest-nodes (drop-while #(hla-primitive (:hla %)) nodes)]
;      (local-immediate-refinements (first rest-nodes) (map :hla (next rest-nodes))))))


(defmethod search/primitive-refinement ::TopDownForwardNode [node]
  (when-not (:first-np node)
;  (when-let [act-seq
;	     (loop [act-seq '()
;		    node node]
;	       (if (= (:class node) ::TopDownForwardRootNode)
;		   act-seq
;		 (if-let [prim (hla-primitive (:hla node))]
;		     (recur (cons prim act-seq) (:previous node))
;		   false)))]
 ;   (clojure.inspector/inspect-tree node)
    (let [act-seq (remove #(= % :noop)
		   (map (comp hla-primitive :hla) (next (reverse (util/iterate-while :previous node))))) 
;	  lower (get-valuation-lower-bound (get-pessimistic-valuation node))
	  upper (get-valuation-upper-bound (get-optimistic-valuation node))] 
 ;     (util/assert-is (= lower upper))
      [act-seq upper])))

;; Only primitive nodes can be solutions, by definition optimal ...
(defmethod search/extract-optimal-solution ::TopDownForwardNode [node] 
  (when (and (not (:first-np node))
	     (> (search/upper-reward-bound node) Double/NEGATIVE_INFINITY))
;	     (> (search/lower-reward-bound node) Double/NEGATIVE_INFINITY))
    (search/primitive-refinement node)))


(defmethod search/node-str ::TopDownForwardNode [node] 
  (util/str-join " " (map (comp hla-name :hla) (next (reverse (util/iterate-while :previous node))))))




;(defmethod search/node-parent ::TopDownForwardNode [node] 
;  Not implemented

;(defmethod search/node-depth ::TopDownForwardNode [node] 
;  (count (:act-seq ^(:state node))))

;(defmethod search/node-first-action ::TopDownForwardNode [node]
;  (nth (:act-seq ^(:state node)) 0))



















(defn- get-and-check-sol [initial-hla]
  (map :name
       (first
	(envs/check-solution (hla-environment initial-hla)
	  (edu.berkeley.ai.search.algorithms.textbook/a-star-search
	   (make-initial-top-down-forward-node initial-hla)))))) 


(require '[edu.berkeley.ai.domains.nav-switch :as nav-switch])
(require '[edu.berkeley.ai.domains.strips :as strips])
(require '[edu.berkeley.ai.domains.warehouse :as warehouse])
(require '[edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as strips-hierarchies])
(require '[edu.berkeley.ai.search.algorithms.textbook :as textbook])


(def *flat-ns* (nav-switch/make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *flat-ns-sol* ['left 'flip 'down])

(def *strips-ns* (nav-switch/make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *strips-ns-sol* '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]])

(def *flat-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 1))))))
(def *strips-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) 1))))))


(def *simplifiers* [identity 
		     strips/constant-predicate-simplify
		     (comp strips/flatten-strips-instance strips/constant-predicate-simplify)])

(util/deftest top-down-nav-switch
   (util/testing "flat hierarchy, non-strips"
     (util/is (= *flat-ns-sol* (get-and-check-sol (get-flat-hierarchy *flat-ns*))))
     (util/is (= *flat-ns-sol* (get-and-check-sol (get-flat-hierarchy *flat-ns* *flat-ns-heur*)))))
   (util/testing "flat hierarchy, strips"
     (util/is (= *strips-ns-sol*
       (get-and-check-sol (get-flat-hierarchy *strips-ns* *strips-ns-heur*))))
     (doseq [simplifier *simplifiers*]
       (util/is (= *strips-ns-sol*
	 (get-and-check-sol (get-flat-hierarchy (simplifier *strips-ns*)))))))
   (util/testing "flat-strips hierarchy"
     (util/is (= *strips-ns-sol*
       (get-and-check-sol (strips-hierarchies/get-flat-strips-hierarchy *strips-ns* *strips-ns-heur*))))
     (doseq [simplifier (butlast *simplifiers*)]
       (util/is (= *strips-ns-sol*
	 (get-and-check-sol (strips-hierarchies/get-flat-strips-hierarchy (simplifier *strips-ns*)))))))
   (util/testing "Ordinary strips hierarchy"
     (doseq [simplifier (butlast *simplifiers*)]
       (util/is (= *strips-ns-sol*
	 (get-and-check-sol (get-hierarchy nav-switch/*nav-switch-hierarchy* (simplifier *strips-ns*))))))))		 

(def *strips-wh* (warehouse/make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))
(def *strips-wh-sols* 
  #{'((get-l a table0 x0 x1 y1) (left x1 x0 y1) (turn-r x0 y1) (put-r a table1 x1 x0 y0 y1))
	 '((get-l a table0 x0 x1 y1) (turn-r x1 y1) (left x1 x0 y1) (put-r a table1 x1 x0 y0 y1))}) 			      

(util/deftest top-down-warehouse
 (util/testing "flat-strips hierarchy"
   (doseq [simplifier (butlast *simplifiers*)
	   maker [strips-hierarchies/get-flat-strips-hierarchy 
		  #(get-hierarchy warehouse/*warehouse-hierarchy-unguided* %)]]
;     (println simplifier maker (map :name (first (textbook/a-star-search (tdf-node (maker (simplifier *strips-wh*)))))))
     (util/is (*strips-wh-sols* (get-and-check-sol (maker (simplifier *strips-wh*))))))))

      

(comment 
  (let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])] 
    (map :name (first (a-star-search 
    (make-initial-top-down-forward-node 
     :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation
     (instantiate-hierarchy
	    (parse-hierarchy "/Users/w01fe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env)) 
    ))))



(let [domain (make-nav-switch-strips-domain)
	env    (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])
	    node
    (make-initial-top-down-forward-node 
     :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation
     (instantiate-hierarchy
	    (parse-hierarchy "/Users/w01fe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy"
			     domain)
	    env))] 
        (map #(vector (search/node-str %) (reward-bounds %)) (take 80 (all-refinements node (make-queue-pq) (constantly 0)))))

(let [domain (make-nav-switch-strips-domain), env (constant-predicate-simplify (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4])), node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation (instantiate-hierarchy (parse-hierarchy "/Users/w01fe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch.hierarchy" domain) env) )] (time (second (a-star-search node))))
;(interactive-search node (make-queue-pq) (constantly 0)))

(u util envs search search.algorithms.textbook angelic angelic.hierarchies domains.nav-switch domains.strips angelic.hierarchies.strips-hierarchies util.queues domains.warehouse)

; Flat hierarchies
(let [env (make-nav-switch-env 6 6 [[1 1]] [5 0] true [0 5]), node (make-initial-top-down-forward-node :edu.berkeley.ai.angelic/ExplicitValuation (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 4))))) ) env))] (time (second (a-star-search node))))

(let [env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]), node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic/ExplicitValuation (instantiate-hierarchy (make-flat-hierarchy-schema  (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env))] (time (second (a-star-search node))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]),  node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (get-strips-state-pred-val state 'aty)) 1) 4))))) ) env))] (time (second (a-star-search node))))

(let [domain (make-nav-switch-strips-domain), env (make-nav-switch-strips-env 5 5 [[1 1]] [4 0] true [0 4]),  node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0) ) env))] (time (second (a-star-search node))))



(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]])),  node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (make-flat-strips-hierarchy-schema domain (constantly 0)) env))] (time (second (a-star-search node))))

(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (make-initial-top-down-forward-node  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation  (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" (make-warehouse-strips-domain)) env))] (time (second (a-star-search node))))

(let [domain (make-warehouse-strips-domain), env (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])),  node (tdf-node (get-hierarchy  "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy" env))] (time (second (a-star-search node))))

  )


(comment 
 ; Speed analysis, 6x6 nav-switch, no heuristic
 ; explicit domain, no hierarchy  : 3.2 s
 ; strips   domain, no hierarchy  : 3.5 s
 ; strips   domain, no hierarchy  : 2.5 s  (flattened and simplified)
 ; explicit domain, flat hierarchy: 11.4 s
 ; strips   domain, flat hierarchy: 14.6 s (13.3 flat/simple)
 ; strips domain, strips flat hier: 152 s
 ; strips comain, constant simplified, grounded strips flat hier: 35 s.
 ;                               (un-simplified: 118)
          ;           (still no real successor generator...)
          ; without cs, 80% time in rg
          ; with, 40% time in rg, 50% in upper-reward-bound
 ; -- long way to go 

 ; First, look at diff between no hier and flat for explicit.  
 ; roughtly same number of "next-s"- just diff order? 
   ; Twice as many nodes on stack, since primitives generated
   ; Overhead of creating valuation objects, hashing constituent states, ...
   
 ; Now, look at strips-flat-hier
  ; 2/3 time going to refinement-instantiations!!
  ; 1/3 to clause-consistent-mappings
    ; Reasonable, since primitive args must be figured out each time (hierarchy saves!)


 )

