(ns edu.berkeley.ai.angelic.hierarchies.online-algorithms
  (:use clojure.test edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hierarchies)
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search]]
	    [edu.berkeley.ai.util.queues :as queues]
	    [edu.berkeley.ai.search.algorithms.real-time :as real-time]
	    [edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees :as alts]
	    [edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as sh])
  )

; 
; Note about consistency with AHLRTA* -- have a flag on descriptions for
; consistent?, raise extra errors when true ?


; Need to subtype ALT nodes so we can check for repeated states.
(derive ::AHLRTAALTPlanNode ::alts/ALTPlanNode)

(defn- make-initial-ahlrta-alt-node [env initial-plan memory high-level-hla-set alt-arg-map]
  (let [initial-plan (map #(assoc-in % [:hierarchy :problem-instance] env) initial-plan) 
	node (alts/alt-node initial-plan (assoc alt-arg-map :node-type ::AHLRTAALTPlanNode))]
    (util/assert-is (= (count initial-plan) 2))
    (update-in 
     (update-in node [:alt] #(assoc % :memory memory :high-level-hla-set high-level-hla-set))
     [:plan]
     #(assoc-in (assoc-in (assoc % :g-rew 0) [:previous :g-rew] 0) [:previous :previous :g-rew] 0))))
;    (assoc node :alt (assoc (:alt node) :memory memory :high-level-hla-set high-level-hla-set)
;	        :plan (assoc (:plan node) 
;			:g-rew 0
;			:previous (assoc (:previous (:plan node)) :g-rew 0)))))

(defmethod alts/construct-immediate-refinement ::AHLRTAALTPlanNode [node previous actions alt parent-depth name was-tight?]
;  (println (search/node-str {:class ::alts/ALTPlanNode :plan previous}) (map hla-name actions))
  (if (empty? actions) 
      (alts/make-alt-plan-node (:class node) alt name previous (inc parent-depth))
    (let [nxt (alts/get-alt-node alt (first actions) previous was-tight?)
	  nxt    (assoc nxt
		   :g-rew (+ (util/safe-get previous :g-rew)
			     (if (contains? (util/safe-get alt :high-level-hla-set) (util/safe-get-in nxt [:hla :schema :name]))
			         0
			       (- (valuation-max-reward (alts/optimistic-valuation nxt))
				  (valuation-max-reward (alts/optimistic-valuation previous))))))
	  prim?  (util/safe-get nxt :primitive?)
	  states              (when prim? (explicit-valuation-map (alts/optimistic-valuation nxt)))
	  [state rew-so-far]  (when prim? (util/assert-is (<= (count states) 1)) (first states))
	  rew-to-go           (when state (get (util/safe-get alt :memory) state))]
    ;  (when prim? (util/print-debug 2 "Found primitive prefix at " (search/node-str {:class ::alts/ALTPlanNode :plan nxt}) " with " (count states) " states:" (hash state) (get (util/safe-get alt :memory) state)))
      (util/print-debug 4 "Considering action" (hla-name (first actions)) " with prev val " (alts/optimistic-valuation previous))
     (if rew-to-go
	(do (util/print-debug 2 "Found known state at " (search/node-str {:class ::alts/ALTPlanNode :plan nxt}))
	    (search/adjust-reward (alts/make-alt-plan-node (:class node) alt name nxt (inc parent-depth)) (+ rew-so-far rew-to-go)))
      (if (and (or (> (valuation-max-reward (alts/optimistic-valuation nxt)) Double/NEGATIVE_INFINITY)
		   (and (util/sref-set! (:fate ^nxt) :dead) false))
	       (or (next actions) 
		   (not (util/sref-get (:was-final? ^nxt)))
		   (= :full (:graph? alt))) ; Eliminate duplicates.
	       (or (not (:graph? alt)) 
		   (alts/graph-add-and-check! alt nxt (next actions) 
					 name)))
	  (recur node nxt (next actions) alt parent-depth name was-tight?)
	(util/print-debug 3 "Late prune at" (search/node-str {:class ::alts/ALTPlanNode :plan nxt})
			  (map hla-name (next actions)) 
			  " with " (valuation-max-reward (alts/optimistic-valuation nxt)) (not (:graph? alt))
			  ;(map println (map optimistic-valuation (util/iterate-while :previous nxt)))
;			  (optimistic-valuation (:previous (:previous nxt)))
			  ))))))



; TODO:  tiebreak by lower-bound/priority-fn?

; consistency, etc. improvements; better than ICAPS?

; Inconsistencies can arise when we visit a state, then a neighbor, then a state again,
; when the bound we got for neighbor is too optimistic, or pruning is avoided.
  ; Plus, simple changes in queue ordering can affect pruning.
  ; Convergence is still guaranteed.
  ; Simple example: put-r leads to known state, so is ignored.
  ; When current state is known, up-down is cut off.
   ; Otherwise, up-down-putr represents best plan for pruning bound; 
    ; we only get it when we don't know current state.
  ; TODO: way to fix this? 

; e.g., inconsistency with (debug 1 (ahlrta-star-search (get-hierarchy *warehouse-hierarchy* (nth *icaps-ww* 5)) 100 70 '#{act move-blocks} {:graph? :bhaskara} 6 '{act 1 'move-blocks 1 'move-to 1 'navigate 2 'nav 3}))

; No evidence that either "improvement" (max primitives, more-refined locking in) help, over wide variety of 
; warehouse instances. ..
(defn ahlrta-star-search 
  "AHLRTA* search from ICAPS '08.  
    max-primitives specifies max # of legal primitives, used to throw away
      refinements as specified in the paper.  Nil = don't throw anything away.
      ref-level-map specifies whether to include other described improvement, 
      locking in only when plan is more refined than last locked-in plan.
      This amounts to tie-breaking towards plans with greater ref-level, which
      is the sum of the ref-levels of the actions in the plan."
  ([initial-plan max-steps max-refs] 
     (ahlrta-star-search initial-plan max-steps max-refs #{'act}))
  ([initial-plan max-steps max-refs high-level-hla-set] 
     (ahlrta-star-search initial-plan max-steps max-refs high-level-hla-set {:ref-choice-fn alts/first-choice-fn}))
  ([initial-plan max-steps max-refs high-level-hla-set alt-arg-map]
     (ahlrta-star-search initial-plan max-steps max-refs high-level-hla-set alt-arg-map nil nil))
  ([initial-plan max-steps max-refs high-level-hla-set alt-arg-map max-primitives ref-level-map]
     (let [initial-plan (sh/convert-to-prim-act-strips-hla initial-plan)
	   memory (HashMap.)]
       (real-time/real-time-search
	(hla-environment (first initial-plan))
	max-steps
	(fn [env]
;	  (println memory "\n\n\n" (envs/get-initial-state env) "\n\n" )
	  (let [node (make-initial-ahlrta-alt-node env initial-plan memory high-level-hla-set alt-arg-map)
		pq   (queues/make-tree-search-pq)]
	    (doseq [nn (search/immediate-refinements node)] ; Start by populating with prim-then-act plans
	      (queues/pq-add! pq nn (- (search/upper-reward-bound nn))))
	    (let [ref-limit (int (* max-refs (if max-primitives (/ (queues/pq-size pq) max-primitives) 1)))
		  _ (util/print-debug 1 "Allowing" ref-limit "refinements.")
		  [g n f]  
		(loop [max-refs ref-limit
			 g-n-f [Double/POSITIVE_INFINITY :dummy Double/POSITIVE_INFINITY]]
		  (util/assert-is (not (queues/pq-empty? pq)) "dead end!")
		  (let [[n nnf] (queues/pq-remove-min-with-cost! pq)
			ra? (search/reward-adjusted-node? n)
			nf (- nnf)]
		    (if (zero? max-refs) (assoc g-n-f 2 nf) ;g-n-f
		      (if (or ra? (search/extract-optimal-solution n))
			  [(if ra? :ra :opt) (if ra? (search/ra-node-base n) n) nf]
			(let [ng     (+ (util/safe-get-in n [:plan :g-rew])
					(* 0.00000001 (if (not ref-level-map) 0
					  (apply + (map #(get ref-level-map (first (hla-name (:hla %))) 4)
							(butlast (util/iterate-while :previous (:plan n))))))))
			      next-g-n-f  (if (< ng (nth g-n-f 0)) [ng n nf] g-n-f)]
			  (util/print-debug 2 "Refining" 0 (search/node-str n) "with g =" ng ", f =" nf 
					    (if (not (identical? g-n-f next-g-n-f)) (str "; locking in " )))
			  (doseq [nn (search/immediate-refinements n)] 
			    (queues/pq-add! pq nn (- (min nf (search/upper-reward-bound nn))))) ; enforce consistency
			  (recur (dec max-refs) next-g-n-f))))))]
;	      (util/assert-is (<= f (or (.get memory (envs/get-initial-state env)) Double/POSITIVE_INFINITY)))
	      (util/print-debug 1 "Intending plan" (search/node-str n) ", g =" g ", f =" f) 
	      (let [old-f (or (.get memory (envs/get-initial-state env)) Double/POSITIVE_INFINITY)]
		(when (> f old-f) 
		  (util/print-debug 1 "Warning: inconsistency detected!")
		;  (throw (Exception. "Inconsistency!"))
		  )
		(.put memory (envs/get-initial-state env) (min f old-f)))
	      (search/node-first-action n))))))))
	      

(comment 
(debug 1 (ahlrta-star-search (get-hierarchy *warehouse-hierarchy* (nth *icaps-ww* 5)) 100 100 #{'act 'move-blocks} {:graph? :full})) 

(debug 1 (ahlrta-star-search (get-hierarchy *warehouse-hierarchy* (nth *icaps-ww* 5)) 100 100 '#{act} {:graph? :full} 6 '{act 1 'move-blocks 1 'move-to 1 'navigate 2 'nav 3}))
 )





; And, improved version? 
 ; Can even keep searching, after we've found memory state, to refine state value!
   ; To do this, though, can't cut things off in construct-immediate-refinement as now.
   ; If there are multiple states along path ... ?

(defn- make-initial-ahlrta2-alt-node [env initial-plan alt-arg-map ]
    (update-in (alts/alt-node (map #(assoc-in % [:hierarchy :problem-instance] env) initial-plan) alt-arg-map) [:plan]
      (fn [n] (update-in (assoc n :g-so-far 0 :min-f-to-go Double/POSITIVE_INFINITY) [:previous]
	(fn [n2] (update-in (assoc n2 :g-so-far 0 :min-f-to-go Double/POSITIVE_INFINITY) [:previous]
	   #(assoc % :g-so-far 0 :min-f-to-go Double/POSITIVE_INFINITY)))))))

;    (assoc node :plan (assoc (:plan node) 
;			:g-so-far 0 :min-f-to-go Double/POSITIVE_INFINITY
;			:previous (assoc (:previous (:plan node)) :g-so-far 0 :min-f-to-go Double/POSITIVE_INFINITY)))))

;; TODO: think about interaction with graph
(defn- postprocess-plan-known-states 
  "Push out values for known states, and return [new-node f [state rew-to-state]-seq], only for new parts of plan.
   Annotate plan with :g-rew and :min-f-to-go as we go along."
  [node #^HashMap memory high-level-hla-set]
  (util/print-debug 3 "Processing refinement" (search/node-str node) "with f =" (search/upper-reward-bound node))
;  (println (search/node-str node))
  (let [new-nodes (reverse (take-while #(not (contains? % :g-so-far)) (util/iterate-while :previous (:plan node))))]
;    (println (map (comp hla-name :hla) new-nodes))
    (loop [previous        (:previous (first new-nodes)), 
	   nodes           new-nodes, 
	   state-rew-pairs nil]
      (if (empty? nodes)
         (do 
	   (when (< (util/safe-get previous :min-f-to-go) 0) 
	     (util/print-debug 2 "Adjusting reward of " (search/node-str node) "downward from" (search/upper-reward-bound node) 
			       "by" (util/safe-get previous :min-f-to-go)))
	   [(assoc node :plan previous)
	    (+ (search/upper-reward-bound node) (min 0 (util/safe-get previous :min-f-to-go)))
	    state-rew-pairs])
        (let [node  (first nodes)
	      hl?   (contains? high-level-hla-set (util/safe-get-in node [:hla :schema :name]))
	      prim? (util/safe-get node :primitive?)
	      states                (when prim? (explicit-valuation-map (alts/optimistic-valuation node)))
	      [state s-rew-so-far]  (when prim? (util/assert-is (= 1 (count states))) (first states))
	      s-rew-to-go           (or (and prim? (get memory state)) Double/POSITIVE_INFINITY)
	      step-rew           (- (valuation-max-reward (alts/optimistic-valuation node))
	  			  (valuation-max-reward (alts/optimistic-valuation previous)))
	      prev-g-so-far      (util/safe-get previous :g-so-far)
	      prev-min-f-to-go   (util/safe-get previous :min-f-to-go)
	      min-f-to-go        (min (- prev-min-f-to-go step-rew) s-rew-to-go)
	      node  (assoc node
		      :previous previous
		      :g-so-far    (+ prev-g-so-far (if hl? 0 step-rew))
		      :min-f-to-go min-f-to-go)]
;	  (println (hla-name (:hla node)))
	  (when (and prim? (< min-f-to-go s-rew-to-go))
;	    (when (< min-f-to-go (get *real-dists* state))
;		      (def *memory* memory)
;		      (def *state-rews* state-rew-pairs)
;		      (def *node* node)
;		      (util/assert-is (>= min-f-to-go (get *real-dists* state)) "TWO"))
	    (.put memory state min-f-to-go))
	  (recur node (rest nodes) (if prim? (cons [state s-rew-so-far] state-rew-pairs) state-rew-pairs)))))))
		    

      

; TODO: still must handle goal plan (add assertion to make sure knowns don't mess it up!)
; TODO: option to do final push or not?
(defn improved-ahlrta-star-search 
  ([initial-plan max-steps max-refs] 
     (improved-ahlrta-star-search initial-plan max-steps max-refs #{'act}))
  ([initial-plan max-steps max-refs high-level-hla-set] 
     (improved-ahlrta-star-search initial-plan max-steps max-refs high-level-hla-set {}))
  ([initial-plan max-steps max-refs high-level-hla-set alt-arg-map]
     (let [initial-plan (sh/convert-to-prim-act-strips-hla initial-plan)
	   memory (HashMap.)]
;       (def *init* initial-hla)
       (real-time/real-time-search
	(hla-environment (first initial-plan))
	max-steps
	(fn [env]
	  (let [state-rews (HashMap.)
		pq   (queues/make-tree-search-pq)]
	    (queues/pq-add! pq (make-initial-ahlrta2-alt-node env initial-plan alt-arg-map) Double/NEGATIVE_INFINITY) 
	    (.put state-rews (envs/get-initial-state env) 0)
	    (let [[g n f]  
		(loop [max-refs max-refs
			 g-n-f [Double/POSITIVE_INFINITY :dummy Double/POSITIVE_INFINITY]]
		  (util/assert-is (not (queues/pq-empty? pq)) "dead end!")
		  (if (zero? max-refs) 
		      (let [best-f (- (second (queues/pq-remove-min-with-cost! pq)))]
			(util/assert-is (<= best-f (nth g-n-f 2)))
			(assoc g-n-f 2 best-f)) ; Best possible bound.
		    (let [[n nnf] (queues/pq-remove-min-with-cost! pq)
			  nf (- nnf)]
		      (if (search/extract-optimal-solution n)
			  (do
;			    (util/print-debug 1 "Returning optimal" (search/node-str n) ", f =" nf) 
			    (util/assert-is (= nf (search/upper-reward-bound n)))
			    [:OPTIMAL n nf])
			(let [ng          (util/safe-get-in n [:plan :g-so-far])
			      next-g-n-f  (if (< ng (nth g-n-f 0)) [ng n nf] g-n-f)]
			  (util/print-debug 2 "Refining" (search/node-str n) "with g =" ng ", f =" nf 
					    (if (not (identical? g-n-f next-g-n-f)) "; locking in" ""))
			  (doseq [nn (search/immediate-refinements n)]
			    (let [[nxt nxt-f sr-seq] (postprocess-plan-known-states nn memory high-level-hla-set)]
			      (doseq [[s r] sr-seq]
				(.put state-rews s (max r (get state-rews s Double/NEGATIVE_INFINITY))))
			      (queues/pq-add! pq nxt (- (min nf nxt-f))))) ; enforce consistency
			  (recur (dec max-refs) next-g-n-f))))))]
	        (util/print-debug 1 "Intending plan" (search/node-str n) " with g =" g, "f =" f, "Final bound =" f)
		(doseq [[s r] state-rews]
		  (let [mem-val (get memory s Double/POSITIVE_INFINITY)
			new-val (- f r)]
		    (when (< new-val mem-val)
;		      (when (< new-val (get *real-dists* s))
;			(def *env* env)
;			(def *memory* memory)
;			(def *state-rews* state-rews)
;			(def *node* n)
;			(util/assert-is (>= new-val (get *real-dists* s)) "one %s" (envs/state-str env s)))
		      (util/print-debug 4 "Reducing reward of state from" mem-val "to" new-val (str "\n" (envs/state-str env s)))
		      (.put memory s new-val))))
		(search/node-first-action n))))))))


(comment ;Some heavy debugging stuff


(def #^HashMap *real-dists* (HashMap.))

(comment 
  (let [#^HashMap rd *real-dists*, inits
	(for [bpos [0 2 3]
		[gpos fr] [[[0 2] true] [[2 2] false]]]
	  (constant-predicate-simplify (make-warehouse-strips-env 4 4 gpos fr {bpos '[b] 1 '[a c]} nil ['[table1 table0]])))
	as (get-action-space (first inits))]
    (loop [gen (map get-initial-state inits)
	   rew 0] (println rew)
      (doseq [s gen] (.put rd s rew))
      (let [next
	    (for [s gen
		  ss (successor-states s as)
		  :when (not (.containsKey rd ss))]
	      ss)]
	(if (empty? next) rew (recur next (dec rew))))))

;    (doseq [init inits] (println (state-str init (get-initial-state init)) "\n")))

  )

(let [env *env* memory *memory* initial-hla *init* ref-choice-fn alts/first-choice-fn cache? true graph? true max-refs 100 high-level-hla-set '#{act move-blocks move-block move-to}]
  (binding [util/*debug-level* 3]
    (let [state-rews (HashMap.)
		pq   (queues/make-tree-search-pq)]
	    (queues/pq-add! pq (make-initial-ahlrta2-alt-node env initial-hla ref-choice-fn cache? graph?) Double/NEGATIVE_INFINITY) 
	    (.put state-rews (envs/get-initial-state env) 0)
	    (let [[g n f]  
		(loop [max-refs max-refs
			 g-n-f [Double/POSITIVE_INFINITY :dummy Double/POSITIVE_INFINITY]]
		  (util/assert-is (not (queues/pq-empty? pq)) "dead end!")
		  (if (zero? max-refs) 
		      (let [best-f (- (second (queues/pq-remove-min-with-cost! pq)))]
			(util/assert-is (<= best-f (nth g-n-f 2)))
			(assoc g-n-f 2 best-f)) ; Best possible bound.
		    (let [[n nnf] (queues/pq-remove-min-with-cost! pq)
			  nf (- nnf)]
		      (if (search/extract-optimal-solution n)
			  (do
			    (util/print-debug 2 "Returning optimal" (search/node-str n) ", f =" nf) 
			    (when-not (= nf (search/upper-reward-bound n))
			      (def *env* env)
			      (def *memory* memory)
			      (def *state-rews* state-rews)
			      (def *node* n)
			      (util/assert-is (= nf (search/upper-reward-bound n))))
			    [:term n nf])
			(let [ng          (util/safe-get-in n [:plan :g-so-far])
			      next-g-n-f  (if (< ng (nth g-n-f 0)) [ng n nf] g-n-f)]
			  (util/print-debug 2 "Refining" (search/node-str n) "with g =" ng ", f =" nf 
					    (if (not (identical? g-n-f next-g-n-f)) "; locking in" ""))
			  (doseq [nn (search/immediate-refinements n)]
			    (util/print-debug 3 "Got ref " (search/node-str nn))
			    (let [[nxt nxt-f sr-seq] (postprocess-plan-known-states nn memory high-level-hla-set)]
			      (doseq [[s r] sr-seq]
				(.put state-rews s (max r (get state-rews s Double/NEGATIVE_INFINITY))))
			      (queues/pq-add! pq nxt (- (min nf nxt-f))))) ; enforce consistency
			  (recur (dec max-refs) next-g-n-f))))))]
	        (util/print-debug 2 "Final bound: " f)
		(doseq [[s r] state-rews]
		  (let [mem-val (get memory s Double/POSITIVE_INFINITY)
			new-val (- f r)]
		    (when (< new-val (get *real-dists* s))
		      (def *env* env)
		      (def *memory* memory)
		      (def *state-rews* state-rews)
		      (def *node* n)
		      (throw (Exception.))
		      )
		    (when (< new-val mem-val)
		      (util/print-debug 4 "Reducing reward of state from" mem-val "to" new-val (str "\n" (envs/state-str env s)))
		      (.put memory s new-val))))
		(search/node-first-action n)))))

)
; (binding [*debug-level* 1] (ahlrta-star-search (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 5 5 [[1 1 ]] [0 4] false [4 0]))) 10 10 #{'act 'go}))

     
; (second (binding [*debug-level* 2] (improved-ahlrta-star-search (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))) 10 10 #{'act 'move-blocks 'move-block 'move-to})))

; (second (binding [*debug-level* 1] (improved-ahlrta-star-search (get-flat-strips-hierarchy (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]])) [:warehouse-act]) 100 100 #{'act 'move-blocks 'move-block 'move-to})))

; (let [ds (parse-description [:warehouse-act] (make-warehouse-strips-domain) nil) inst (constant-predicate-simplify (make-warehouse-strips-env 4 4 [0 1] true { 3 '[a b]} 'c ['[a c table1]])) val (make-initial-valuation :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation inst) d (ground-description (instantiate-description-schema ds inst) nil)] (println (state-str inst (get-initial-state inst))) (progress-optimistic val d))



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


(deftest hierarchical-algorithms
   (doseq [[inst-n rew h env] [*ns-inst* *wh-inst*]
	   cache?      [false true]
	   graph?      [false true :full]
	   [sf-n alg strict?] [["aha" aha-star-search true] ["ahss-inf" ahss-search false] ["ahss-=" #(ahss-search % rew) true]]]
     (testing (str inst-n " " cache? " " graph? " " sf-n)
;       (println inst-n cache? graph? sf-n)
       (is ((if strict? = >=) rew  
	 (second (envs/check-solution env (alg (alts/alt-node (get-hierarchy h env) cache? graph?)))))))))

 )
      




(comment 
 (dotimes [_ 2] (let [env (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 20 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))] (doseq [h [*nav-switch-hierarchy* *nav-switch-hierarchy-improved*]] (let [node (get-hierarchy h env )] (println h) (dotimes [_ 1] (time (println (second (aha-star-search (alt-node node))))) (time (println (second (ahss-search (alt-node node))))) )))))
 )


  
