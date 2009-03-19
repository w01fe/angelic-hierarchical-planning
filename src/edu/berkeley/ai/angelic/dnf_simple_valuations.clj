(ns edu.berkeley.ai.angelic.dnf-simple-valuations
  (:use [edu.berkeley.ai.angelic :as angelic])
  (:import [java.util HashMap])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
            [edu.berkeley.ai.util.propositions :as props]
	    ))

;;; A set of conjunctive clauses, maps from vars to :true or :unknown  (not present = :false)

; TODO: think about splitting out constant part of state.


(derive ::DNFSimpleValuation :edu.berkeley.ai.angelic/PropositionalValuation)

(defstruct dnf-simple-valuation :class :dnf :bound)

(defn make-dnf-simple-valuation [dnf bound]
;  (prn "DNF!")
  (if (not (empty? dnf))
      (struct dnf-simple-valuation ::DNFSimpleValuation (util/to-set dnf) bound)
    *pessimal-valuation*))
;    (struct dnf-simple-valuation ::DNFSimpleValuation nil Double/NEGATIVE_INFINITY)))


  
(defmethod state->valuation     ::DNFSimpleValuation [type state]
  (make-dnf-simple-valuation (list (util/map-map #(vector % :true) state)) 0))

(defmethod get-valuation-lower-bound ::DNFSimpleValuation [val] (:bound val))

(defmethod get-valuation-upper-bound ::DNFSimpleValuation [val] (:bound val))

(defmethod empty-valuation?       ::DNFSimpleValuation [val] (empty? (:dnf val)))

(defn- clause-instantiations [clause]
  (loop [insts [#{}]
	 pairs (seq clause)]
    (if (empty? pairs) insts
      (let [[var val] (first pairs)]
	(cond (= val :true)
  	        (recur (map #(conj % var) insts) (next pairs))
	      (= val :unknown)
	        (recur (concat (map #(conj % var) insts) insts) (next pairs))
	      :else (throw (IllegalArgumentException.)))))))
	  

(defmethod explicit-valuation-map ::DNFSimpleValuation [val]
  (into {}
    (map #(vector % (:bound val))
      (util/forcat [clause (:dnf val)]
	(clause-instantiations clause)))))


(defn restrict-clause [clause pos neg]
  (when-let [after-pos
	     (loop [pos pos clause clause]
	       (cond (empty? pos)                   clause
		     (contains? clause (first pos)) (recur (next pos) (assoc clause (first pos) :true))
		     :else nil))]
    (loop [neg neg clause after-pos]
      (cond (empty? neg)                       clause
	    (= :true (get clause (first neg))) nil
	    :else  (recur (next neg) (dissoc clause (first neg)))))))

(defmethod restrict-valuation       [::DNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (let [pos (envs/get-positive-conjuncts con)
	neg (envs/get-negative-conjuncts con)]
    (make-dnf-simple-valuation 
     (filter identity (for [clause (:dnf val)] (restrict-clause clause pos neg)))
     (:bound val))))

(defmethod get-valuation-states     ::DNFSimpleValuation [val]
  (:dnf val))

(defmethod extract-a-state          ::DNFSimpleValuation [v]
  (when-first [clause (:dnf v)]
    (set (map key (filter (fn [p] (= (val p) :true)) clause)))))

; TODO: special case non-constraint case ?

(defn- do-valuation->pred-maps [val]
;  (doall
  (for [clause (util/safe-get val :dnf)]
    (let [true-map (HashMap.) poss-map (HashMap.)]
      (doseq [[#^clojure.lang.APersistentVector pred stat] clause]
	(let [#^HashMap m (if (= stat :true) true-map poss-map)
	      pred-name (.get pred 0)]
;	      pred-args (next pred)] 
	  (.put m pred-name (cons pred (.get m pred-name)))))
      [true-map poss-map])));)

(defmethod valuation->pred-maps ::DNFSimpleValuation [val]
  (do-valuation->pred-maps val))


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
