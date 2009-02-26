(ns edu.berkeley.ai.angelic.hierarchies.online-algorithms
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.queues :as queues]
	    [edu.berkeley.ai.search.algorithms.real-time :as real-time]
	    [edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts]
	    [edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as sh])
  )


; (sa/convert-to-prim-act-strips-hla initial-node)


; Need to subtype ALT nodes so we can check for repeated states.
(derive ::AHLRTAALTPlanNode ::alts/ALTPlanNode)

;; TODO: handle g-cost...
(defn- make-initial-ahlrta-alt-node [env initial-node ref-choice-fn cache? graph? memory high-level-hla-set]
  (let [initial-node (assoc initial-node :hierarchy (assoc (:hierarchy initial-node) :problem-instance env)) 
	node (alts/alt-node ::AHLRTAALTPlanNode (hla-default-valuation-type initial-node)
			    initial-node ref-choice-fn cache? graph?)]
    (assoc node :alt (assoc (:alt node) :memory memory :high-level-hla-set high-level-hla-set)
	        :plan (assoc (:plan node) 
			:g-rew 0
			:previous (assoc (:previous (:plan node)) :g-rew 0)))))


(defmethod alts/construct-immediate-refinement ::AHLRTAALTPlanNode [node previous actions alt name ancestors]
  (if (empty? actions) 
      (alts/make-alt-plan-node (:class node) alt name previous ancestors)
    (let [nxt    (alts/get-alt-node alt (first actions) previous)
	  nxt    (assoc nxt
		   :g-rew (+ (util/safe-get previous :g-rew)
			     (if (contains? (util/safe-get alt :high-level-hla-set) (util/safe-get-in nxt [:hla :schema :name]))
			         0
			       (- (get-valuation-upper-bound (alts/optimistic-valuation nxt))
				  (get-valuation-upper-bound (alts/optimistic-valuation previous))))))
	  prim?  (util/safe-get nxt :primitive?)
	  states              (when prim? (explicit-valuation-map (alts/optimistic-valuation nxt)))
	  [state rew-so-far]  (when prim? (util/assert-is (= 1 (count states))) (first states))
	  rew-to-go           (when prim? (get (util/safe-get alt :memory) state))]
      (if rew-to-go
	  (search/adjust-reward (alts/make-alt-plan-node (:class node) alt name nxt ancestors) (+ rew-so-far rew-to-go))  
	(when (or (not (util/safe-get alt :graph?)) 
		  (alts/graph-add-and-check! alt nxt (next actions) name ancestors))
	  (recur node nxt (next actions) alt name ancestors))))))


; TODO: do we need to handle goal separately?  YES.
  ; extract-optimal-solution on nodes
  ; if this or reward-adjusted, return corresponding action immediately.

; TODO:  tiebreak by lower-bound/priority-fn?

;; TODO: two modifications (max-ref discounting, locking in conditions)

;; TODO: how do we compute g-cost of RA??

;; TODO: consistency ?  Can hack it in by just storing min f ever encountered.
(defn ahlrta-star-search 
  ([initial-hla max-steps max-refs] 
     (ahlrta-star-search initial-hla max-steps max-refs #{'act}))
  ([initial-hla max-steps max-refs high-level-hla-set] 
     (ahlrta-star-search initial-hla max-steps max-refs high-level-hla-set alts/first-choice-fn true true))
  ([initial-hla max-steps max-refs high-level-hla-set ref-choice-fn cache? graph?]
     (let [initial-hla (sh/convert-to-prim-act-strips-hla initial-hla)
	   memory (HashMap.)]
       (real-time/real-time-search
	(hla-environment initial-hla)
	max-steps
	(fn [env]
	  (let [node (make-initial-ahlrta-alt-node env initial-hla ref-choice-fn cache? graph? memory high-level-hla-set)
		pq   (queues/make-tree-search-pq)]
	    (doseq [nn (search/immediate-refinements node)] ; Start by populating with prim-then-act plans
	      (queues/pq-add! pq nn (- (search/upper-reward-bound nn))))
	    (loop [max-refs max-refs
		   g-a-f [1 nil 0]]
	      (if (or (zero? max-refs)
		      (queues/pq-empty? pq))
		  (do (.put memory (envs/get-initial-state env) (nth g-a-f 2))
		      (nth g-a-f 1))
		(let [[n nnf] (queues/pq-remove-min-with-cost! pq)
		      nf     (- nnf)
		      ra?    (search/reward-adjusted-node? n)
		      n      (if ra? (search/ra-node-base n) n)
		      ng     (util/safe-get-in n [:plan :g-rew])
		      next-g-a-f  (if (< ng (nth g-a-f 0)) [ng (search/node-first-action n) nf] g-a-f)]
		  (util/print-debug 2 "Refining" (search/node-str n) (if ra? "XXX" "") "with g =" ng ", f =" nf 
				    (if (not (identical? g-a-f next-g-a-f)) (str "; locking in " (:name (nth next-g-a-f 1))) ""))
		  (doseq [nn (search/immediate-refinements n)] 
		    (queues/pq-add! pq nn (- (search/upper-reward-bound nn))))
		  (recur (dec max-refs) next-g-a-f))))))))))
	      

; (binding [*debug-level* 1] (ahlrta-star-search (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 5 5 [[1 1 ]] [0 4] false [4 0]))) 10 10 #{'act 'go}))

     




;; Testing



(comment 

(require '[edu.berkeley.ai.envs :as envs])
(require '[edu.berkeley.ai.domains.nav-switch :as nav-switch])
(require '[edu.berkeley.ai.domains.strips :as strips])
(require '[edu.berkeley.ai.domains.warehouse :as warehouse])
(require '[edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts])
(require '[edu.berkeley.ai.search.algorithms.textbook :as textbook])

(def *ns-inst* ["ns" -27 nav-switch/*nav-switch-hierarchy* 
		(strips/constant-predicate-simplify
		 (nav-switch/make-nav-switch-strips-env 6 6 [[4 0] [3 3] [0 4]] [5 0] true [0 5]))])

(def *wh-inst* ["wh" -6 warehouse/*warehouse-hierarchy*
		 (strips/constant-predicate-simplify 
		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[c] 3 '[d]} nil ['[b d]]))])
;		  (warehouse/make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))])
;		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[d] 3 '[c]} nil ['[a b c]]))])


(util/deftest hierarchical-algorithms
   (doseq [[inst-n rew h env] [*ns-inst* *wh-inst*]
	   cache?      [false true]
	   graph?      [false true :full]
	   [sf-n alg strict?] [["aha" aha-star-search true] ["ahss-inf" ahss-search false] ["ahss-=" #(ahss-search % rew) true]]]
     (util/testing (str inst-n " " cache? " " graph? " " sf-n)
;       (println inst-n cache? graph? sf-n)
       (util/is ((if strict? = >=) rew  
	 (second (envs/check-solution env (alg (alts/alt-node (get-hierarchy h env) cache? graph?)))))))))

 )
      




(comment 
 (dotimes [_ 2] (let [env (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 20 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))] (doseq [h [*nav-switch-hierarchy* *nav-switch-hierarchy-improved*]] (let [node (get-hierarchy h env )] (println h) (dotimes [_ 1] (time (println (second (aha-star-search (alt-node node))))) (time (println (second (ahss-search (alt-node node))))) )))))
 )


  
