(ns edu.berkeley.ai.angelic.dnf-valuations
  (:use [edu.berkeley.ai.angelic :as angelic])
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
            [edu.berkeley.ai.util.propositions :as props]
	    ))

;;; A map from conjunctive clauses (maps from vars to :true or :unknown) to rewards.  (not present = :false)
; DNF simple valuations are like DNF valuations, but the reward is the same for all clauses.
 ; In the pessimistic case min reward is taken, optimistic = max.

; *state->valuation, map->valuation, explicit-valuation-map, restrict-valuation, union-valuations, *empty-valuation?, *valuation-state-reward, *valuation-max-reward-state, *valuation-max-reward, *get-valuation-states, *valuation-subsumes?, progress-exact, regress-state


(derive ::DNFValuation :edu.berkeley.ai.angelic/PropositionalValuation)

(derive ::DNFSimpleValuation ::DNFValuation)
(derive ::DNFPessimisticSimpleValuation ::DNFSimpleValuation)
(derive ::DNFOptimisticSimpleValuation ::DNFSimpleValuation)

(defstruct dnf-valuation :class :clause-map)

(defn make-dnf-valuation [class clause-map]
  (cond (empty? clause-map)             
	  *pessimal-valuation*
	(isa? class ::DNFOptimisticSimpleValuation)
	  (let [max-rew (apply max (vals clause-map))]
	    (struct dnf-valuation class (util/map-vals (constantly max-rew) clause-map)))
	(isa? class ::DNFPessimisticSimpleValuation)
	  (let [min-rew (apply min (vals clause-map))]
	    (struct dnf-valuation class (util/map-vals (constantly min-rew) clause-map)))
	:else 
	  (struct dnf-valuation class clause-map)))

  
(defmethod map->valuation     ::DNFValuation [type m]
  (make-dnf-valuation type (util/map-keys state->clause m)))


(defn- clause-instantiations [clause]
  (loop [insts [#{}]
	 pairs (seq clause)]
    (if (empty? pairs) insts
      (let [[var val] (first pairs)]
	(cond (= val :true)
  	        (recur (map #(conj % var) insts) (next pairs))
	      (= val :unknown)
	        (recur (concat insts (map #(conj % var) insts)) (next pairs))
	      :else (throw (IllegalArgumentException.)))))))

(defmethod explicit-valuation-map ::DNFValuation [val]
  (apply util/merge-best > {}
    (for [[clause bound] (:clause-map val)]
      (map #(vector % bound) (clause-instantiations clause)))))


(defmethod restrict-valuation       [::DNFValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (make-dnf-valuation (:class val)
    (util/merge-best > {}
      (for [[clause bound] (:clause-map val)
	    :let [restricted (restrict-clause clause con)]
	    :when restricted]
	[restricted bound]))))


(defmethod union-valuations         [::DNFValuation ::DNFValuation] [val1 val2]
  (util/assert-is (= (:class val1) (:class val2)))
  (make-dnf-valuation (:class val1) (util/merge-best > (:clause-map val1) (:clause-map val2))))

(defmethod empty-valuation?         ::DNFValuation [v] 
  false)

(defmethod valuation-max-reward-state ::DNFValuation [v]
  (let [[clause rew] (util/first-maximal-element val (:clause-map v))]
    [(minimal-clause-state clause) rew]))

(defmethod valuation-max-reward ::DNFValuation [val] 
  (apply max (vals (:clause-map val))))



;; For now, a valid subsumption map maps predicates to clojure predicates.
; One valuation subsumes another if, for each clause, the best possibly-true value in the latter is subsumed by the best possibly-true value in the former.
; Right now, is limited to single clauses and single-argument predicates.

; Subsumption is a bit tricky for non-simple valuations ...

(defn- extract-clause-subsumption-preds [clause pred-set]
  (if (empty? pred-set) 
      [clause {}]
    (loop [atoms          (keys clause),
	   reduced-clause clause, 
	   sub-map        {}]
      (if (nil? atoms) [reduced-clause sub-map]
	  (let [atom (first atoms)]
	    (if (contains? pred-set (first atom))
 	        (recur (next atoms) 
		       (dissoc reduced-clause atom) 
		       (util/assoc-cons sub-map (first atom) (next atom)))
	      (recur (next atoms) reduced-clause sub-map)))))))


(defmethod get-valuation-states     ::DNFValuation [v subsumption-map]
  (let [subsumption-preds (util/keyset subsumption-map)
	ordered-pairs     (sort-by #(hash (key %)) (:clause-map v))
	subs-pairs        (map #(extract-clause-subsumption-preds (key %) subsumption-preds) ordered-pairs)]
    [(map first subs-pairs)
     {:class ::DNFValuationSI :sub-maps (map second subs-pairs) :rews (map val ordered-pairs)}])) 
      

;; TODO: slow slow slow?
(defmethod valuation-subsumes?     [::DNFValuationSI ::DNFValuationSI] [val1 val2 subsumption-map]
  (and (every? identity (map >= (:rews val1) (:rews val2)))
       (every? identity 
	      (map (fn [sub1 sub2]
		     (every? (fn [[atom-pred [gt-fn eq-fn]]]
			       (every? identity (map gt-fn (get sub1 atom-pred) (get sub2 atom-pred))))
			     subsumption-map))
		   (:sub-maps val1) (:sub-maps val2)))))

(defmethod valuation-equals?     [::DNFValuationSI ::DNFValuationSI] [val1 val2 subsumption-map]
  (and (= (:rews val1) (:rews val2))
       (every? identity 
	      (map (fn [sub1 sub2]
		     (every? (fn [[atom-pred [gt-fn eq-fn]]]
			       (every? identity (map eq-fn (get sub1 atom-pred) (get sub2 atom-pred))))
			     subsumption-map))
		   (:sub-maps val1) (:sub-maps val2)))))

          



(defmethod valuation->pred-maps ::DNFValuation [val]
  (map clause->pred-maps (keys (:clause-map val))))




(defmethod valuation-state-reward ::DNFValuation [v state]
  (let [ordered-clauses (reverse (sort-by val (:clause-map v)))
        good-clauses (filter #(clause-includes-state? (key %) state) ordered-clauses)]
    (if (empty? good-clauses) 
        Double/NEGATIVE_INFINITY
      (val (first good-clauses)))))


(defmethod progress-valuation [::DNFValuation :edu.berkeley.ai.angelic/PropositionalDescription] [v desc]
  (make-dnf-valuation (:class v)
    (apply util/merge-best > {}
	   (for [[clause rew] (:clause-map v),
		 [next-clause step-rew] (progress-clause clause desc)]
	     [next-clause (+ rew step-rew)]))))



;; TODO: make more efficient?
(defmethod regress-state [::DNFValuation :edu.berkeley.ai.angelic/PropositionalDescription :edu.berkeley.ai.angelic/Valuation] 
  [state pre-val desc post-val]
  (let [candidate-pairs
	  (for [[clause rew]             (:clause-map pre-val),
		[result-clause step-rew] (progress-clause clause desc)
		:when (clause-includes-state? result-clause state)]
	    [rew step-rew clause result-clause])]
    (when (seq candidate-pairs)
      (let [[rew step-rew source-clause result-clause] 
	    (util/first-maximal-element #(+ (first %) (second %)) candidate-pairs)]
	(regress-clause-state state source-clause desc [result-clause step-rew])))))	      
  




(defn- test-simple-subsumption [clause-map1 clause-map2 expect-equal-states? expect-subsumes?]
  (let [[states1 sub1] (get-valuation-states (make-dnf-valuation ::DNFValuation clause-map1) nil)
	[states2 sub2] (get-valuation-states (make-dnf-valuation ::DNFValuation clause-map2) nil)]
    (and  (util/same-truth-value?  expect-equal-states? (= states1 states2)))
      (or (not expect-equal-states?)
	  (util/same-truth-value? expect-subsumes? (valuation-subsumes? sub1 sub2 nil)))))

(util/deftest dnf-simple-subsumption
  (util/is (test-simple-subsumption '{{[a 4] :true [b 2] :unknown} 5} '{{[a 4] :true [b 2] :unknown} 4} true true))
  (util/is (test-simple-subsumption '{{[a 4] :true [b 2] :unknown} 5} '{{[a 4] :true [b 2] :unknown} 5} true true))
  (util/is (test-simple-subsumption '{{[a 4] :true [b 2] :unknown} 5} '{{[a 4] :true [b 2] :unknown} 6} true false))
  (util/is (test-simple-subsumption '{{[a 4] :true [b 2] :unknown} 5} '{{[a 4] :true [b 3] :unknown} 5} false false))
  (util/is (test-simple-subsumption '{{[a 4] :true [b 2] :unknown} 5} '{{[a 4] :true [b 2] :true} 5} false false))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :true} 5, {[a 3] :true} 0} true true))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :true} 4, {[a 3] :true} -1} true true))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :true} 5, {[a 3] :true} -5} true true))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :true} 6, {[a 3] :true} -5} true false))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :true} 5, {[a 3] :true} 1} true false))
  (util/is (test-simple-subsumption '{{[a 4] :true} 5, {[a 3] :true} 0} '{{[a 4] :unknown} 5, {[a 3] :true} 1} false false)))

(util/deftest dnf-fancy-subsumption
  (let [sub-info {'a *subsumption-preds-gt* 'b *subsumption-preds-lt*}]
    (util/is (valuation-subsumes? 
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 4] :true [b 1] :unknown} 5}) sub-info))
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 3] :unknown [b 3] :true} 2}) sub-info))
	      sub-info))
    (util/is (not (valuation-subsumes? 
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 4] :true [b 1] :unknown} 2}) sub-info))
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 3] :unknown [b 3] :true} 5}) sub-info))
	      sub-info)))
    (util/is (not (valuation-subsumes? 
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 4] :true [b 5] :unknown} 5}) sub-info))
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 3] :unknown [b 3] :true} 2}) sub-info))
	      sub-info)))
    (util/is (not (valuation-subsumes? 
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 4] :true [b 1] :unknown} 5}) sub-info))
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 5] :unknown [b 3] :true} 2}) sub-info))
	      sub-info)))
    (util/is (valuation-subsumes? 
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[c] :true [a 4] :true [b 1] :unknown} 5}) sub-info))
	      (second (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[c] :true [a 3] :unknown [b 3] :true} 2}) sub-info))
	      sub-info))
    ))


(comment 
  (println (get-valuation-states (make-dnf-valuation ::DNFValuation '{{[a 4] :true} 5, {[a 3] :true} 0}) {}))

(defn intersect-dnf-clauses [c1 c2]
  (loop [ret c1 other (seq c2)]
    (if-let [[atom tv] (first other)]
        (if (= tv :unknown) 
	    (recur ret (next other))
	  (when (get c1 atom)
	    (recur (assoc ret atom :true) (next other))))
      (loop [ret ret other (seq c1)]
	(if-let [[atom tv] (first other)]
	    (if (get c2 atom) 
	        (recur ret (next other))
	      (when-not (= tv :true)
		(recur (dissoc ret atom) (next other))))
	  ret)))))


(defmethod intersect-valuations [::DNFSimpleValuation ::DNFSimpleValuation] [v1 v2]
  (make-dnf-simple-valuation 
   (disj (set (for [c1 (:dnf v1) c2 (:dnf v2)] (intersect-dnf-clauses c1 c2))) nil)
   (:bound v1)))

(defmethod sub-intersect-valuations [::DNFSimpleValuation ::DNFSimpleValuation] [v1 v2]
  (let [c (first (filter identity (for [c1 (:dnf v1) c2 (:dnf v2)] (intersect-dnf-clauses c1 c2))))]
    (util/assert-is (identity c))
    (make-dnf-simple-valuation #{c} (:bound v1))))
 )



