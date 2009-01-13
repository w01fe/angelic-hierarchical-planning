(ns edu.berkeley.ai.angelic.dnf-simple-valuations
  (:refer-clojure)
  (:use clojure.contrib.seq-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.envs edu.berkeley.ai.util.propositions edu.berkeley.ai.angelic edu.berkeley.ai.search.csps))

;;; A set of conjunctive clauses, maps from vars to :true or :unknown  (not present = :false)

; TODO: think about splitting out constant part of state.


(derive ::DNFSimpleValuation :edu.berkeley.ai.angelic/PropositionalValuation)

(defstruct dnf-simple-valuation :class :dnf :bound)

(defn make-dnf-simple-valuation [dnf bound]
  (if-let [dnf (seq dnf)]
      (struct dnf-simple-valuation ::DNFSimpleValuation (set dnf) bound)
    (struct dnf-simple-valuation ::DNFSimpleValuation nil Double/NEGATIVE_INFINITY)))


  
(defmethod make-initial-valuation     ::DNFSimpleValuation [type env]
  (make-dnf-simple-valuation (list (map-map #(vector % :true) (get-initial-state env))) 0))

(defmethod get-valuation-lower-bound ::DNFSimpleValuation [val] (:bound val))

(defmethod get-valuation-upper-bound ::DNFSimpleValuation [val] (:bound val))

(defmethod dead-end-valuation?       ::DNFSimpleValuation [val] (empty? (:dnf val)))



(defn restrict-clause [clause pos neg]
  (when-let [after-pos
	     (loop [pos pos clause clause]
	       (cond (empty? pos)                   clause
		     (contains? clause (first pos)) (recur (rest pos) (assoc clause (first pos) :true))
		     :else nil))]
    (loop [neg neg clause after-pos]
      (cond (empty? neg)                       clause
	    (= :true (get clause (first neg))) nil
	    :else  (recur (rest neg) (dissoc clause (first neg)))))))

(defmethod restrict-valuation       [::DNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (let [pos (get-positive-conjuncts con)
	neg (get-negative-conjuncts con)]
    (make-dnf-simple-valuation 
     (filter identity (for [clause (:dnf val)] (restrict-clause clause pos neg)))
     (:bound val))))


; TODO: full CSP solution ?
; TODO: special case non-constraint case ?
;; TODO TODO: filter domains first in linear time

; 

; To be supported, a value must appear in at least one instantiation of each 
(comment 
(defn filter-domains [clause var-pos var-neg dummy-domains]
  (let [pos-pred-map (map-map-cat #(vector (first %) [(rest %)]) var-pos)
	neg-pred-map (map-map-cat #(vector (first %) [(rest %)]) var-pos)]
    (loop [allowed {}
	   disallowed {}
	   clause (seq clause)]
      (if clause
	  (recur 
	   (if-let [pos (get pos-pred-map (ffirst clause))]
	       ...
	     allowed)
	   
	   (rest clause))
	(map-map 
	 (fn [dummy-var domain]
	   [dummy-var
	    (clojure.set/difference 
	     (clojure.set/intersection domain (get allowed dummy-var))
	     (get disallowed dummy-var))])
	 dummy-domains))))))

(comment 
(defn clause-consistent-mappings [clause var-pos var-neg dummy-domains]
  (let [dummy-seq (seq (filter-domains clause var-pos var-neg dummy-domains))]
    (filter #(restrict-clause clause 
	       (map (partial simplify-atom %) var-pos) 
	       (map (partial simplify-atom %) var-neg))
	    (for [combo (combinations (map second dummy-seq))]
	      (map-map (fn [dummy-map-entry dummy-val] [(first dummy-map-entry) dummy-val])
		       dummy-seq combo)))))
  

(defn clause-consistent-mappings [clause var-pos var-neg dummy-domains]
  (let [dummy-seq (seq dummy-domains)]
    (filter #(restrict-clause clause 
	       (map (partial simplify-atom %) var-pos) 
	       (map (partial simplify-atom %) var-neg))
	    (for [combo (combinations (map second dummy-seq))]
	      (map-map (fn [dummy-map-entry dummy-val] [(first dummy-map-entry) dummy-val])
		       dummy-seq combo)))))
)
; CSP approach cuts time in half for 25x25 nav-switch domains.
(defn clause-consistent-mappings [clause var-pos var-neg dummy-domains]
  (all-csp-solutions (make-conjunctive-propositional-csp dummy-domains var-pos var-neg clause)))

(defmethod valuation-consistent-mappings [::DNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition]
  [opt-val quasi-ground-condition dummy-domains]
  (let [[var-pos ground-pos] (separate #(some is-dummy-var? (rest %)) 
				       (get-positive-conjuncts quasi-ground-condition))
	[var-neg ground-neg] (separate #(some is-dummy-var? (rest %)) 
				       (get-negative-conjuncts quasi-ground-condition))
	opt-val (restrict-valuation opt-val (make-conjunctive-condition ground-pos ground-neg))]
;    (prn dummy-domains ground-pos var-pos ground-neg var-neg opt-val)
    (when-not (dead-end-valuation? opt-val)
      (reduce clojure.set/union #{} (map #(clause-consistent-mappings % var-pos var-neg dummy-domains)
				     (:dnf opt-val))))))

      