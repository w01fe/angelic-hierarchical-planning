(ns edu.berkeley.ai.angelic.dnf-simple-valuations
  (:refer-clojure)
  (:use clojure.contrib.seq-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.envs edu.berkeley.ai.util.propositions edu.berkeley.ai.domains.strips edu.berkeley.ai.angelic))

(defstruct dnf-simple-valuation :class :dnf :bound)

; TODO: think about splitting out constant part of state.

; dnf clauses are maps from vars to :true or :unknown  (not present = :false)

(defn make-dnf-simple-valuation [dnf bound]
  (if-let [dnf (seq dnf)]
      (struct dnf-simple-valuation ::DNFSimpleValuation dnf bound)
    (struct dnf-simple-valuation ::DNFSimpleValuation nil Double/NEGATIVE_INFINITY)))
  
(defmethod make-initial-valuation     ::DNFSimpleValuation [type env]
  (make-dnf-simple-valuation (list (map-map #(vector % :true) (get-initial-state env))) 0))

(defmethod get-valuation-lower-bound ::DNFSimpleValuation [val] (:bound val))
(defmethod get-valuation-upper-bound ::DNFSimpleValuation [val] (:bound val))
(defmethod dead-end-valuation?       ::DNFSimpleValuation [val] (seq (:dnf val)))

(defn restrict-clause [clause pos neg]
  (when-let [after-pos
	     (loop [pos pos clause clause]
	       (cond (empty? pos)                   clause
		     (contains? clause (first pos)) (recur (rest pos) (assoc clause (first pos) :true))
		     :else nil))]
    (loop [neg neg clause clause]
      (cond (empty? pos)                       clause
	    (= :true (get clause (first pos))) nil
	    :else  (recur (rest pos) (dissoc clause (first pos)))))))

(defmethod restrict-valuation       [::DNFSimpleValuation :edu.berkeley.ai.domains.strips/ConjunctiveCondition] [val con]
  (let [pos (get-positive-conjuncts con)
	neg (get-negative-conjuncts con)]
    (make-dnf-simple-valuation 
     (filter identity (for [clause (:dnf val)] (restrict-clause clause pos neg)))
     (:bound val))))


(defn is-dummy-var? [var]
  (and (keyword? var)
       (.startsWith (name var) "?")))

(defmulti valuation-consistent-mappings (fn [val cond dummy-domains] [(:class val) (:class cond)]))

;; TODO TODO: filter domains first in constant time
(defn clause-consistent-mappings [clause var-pos var-neg dummy-domains]
  (let [dummy-seq (seq dummy-domains)]
    (filter #(restrict-clause clause 
	       (map (partial simplify-atom %) var-pos) 
	       (map (partial simplify-atom %) var-neg))
	    (for [combo (combinations (map second dummy-seq))]
	      (map-map (fn [dummy-map-entry dummy-val] [(first dummy-map-entry) dummy-val])
		       dummy-seq combo)))))
  

(defmethod valuation-consistent-mappings [::DNFSimpleValuation :edu.berkeley.ai.domains.strips/ConjunctiveCondition]
  [opt-val quasi-ground-condition dummy-domains]
  (let [[ground-pos var-pos] (separate #(some is-dummy-var? (rest %)) 
				       (get-positive-conjuncts quasi-ground-condition))
	[ground-neg var-neg] (separate #(some is-dummy-var? (rest %)) 
				       (get-negative-conjuncts quasi-ground-condition))
	opt-val (restrict-valuation opt-val (make-conjunctive-condition ground-pos ground-neg))]
    (when-not (dead-end-valuation? opt-val)
      (reduce clojure.set/union (map #(clause-consistent-mappings % var-pos var-neg dummy-domains)
				     (:dnf opt-val))))))

      