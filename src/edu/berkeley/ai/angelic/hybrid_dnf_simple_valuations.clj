(ns edu.berkeley.ai.angelic.hybrid-dnf-simple-valuations
  (:use [edu.berkeley.ai.angelic :as angelic])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
            [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid]]
	    ))

;;; Like DNF simple valuations, but keep a Polytope (orthotope?) for numeric vars.

; TODO: think about splitting out constant part of state.

(defstruct hybrid-dnf-clause :conj :imap)
(defn make-hybrid-dnf-clause [conj imap] (struct hybrid-dnf-clause conj imap))


(derive ::HybridDNFSimpleValuation :edu.berkeley.ai.angelic/PropositionalValuation)
(defstruct hybrid-dnf-simple-valuation :class :clauses)
(defn make-hybrid-dnf-simple-valuation [clauses]
  (if (not (empty? clauses))
      (struct hybrid-dnf-simple-valuation ::HybridDNFSimpleValuation clauses)
    *pessimal-valuation*))


(def *reward-var* [(gensym "reward")]) ; Special dummy variable used to store reward


(defmethod make-initial-valuation     ::HybridDNFSimpleValuation [type env]
  (let [[discrete-atoms numeric-fns] (envs/get-initial-state env)]
    (make-hybrid-dnf-simple-valuation 
     [(make-hybrid-dnf-clause
       (util/map-map #(vector % :true) discrete-atoms)
       (assoc (util/map-vals #(util/make-point-interval %) numeric-fns)
	 *reward-var* 0))])))

(defmethod get-valuation-lower-bound ::HybridDNFSimpleValuation [val] 
  (reduce min (map #(util/safe-get-in % [:imap *reward-var*]) (:clauses val))))

(defmethod get-valuation-upper-bound ::HybridDNFSimpleValuation [val]
  (reduce max (map #(util/safe-get-in % [:imap *reward-var*]) (:clauses val))))

(defmethod empty-valuation?         ::HybridDNFSimpleValuation [val] 
  false)


;; TODO!!
(defmethod restrict-valuation       [::HybridDNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (throw (UnsupportedOperationException.))) 
  
(defmethod explicit-valuation-map ::HybridDNFSimpleValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod get-valuation-states   ::HybridDNFSimpleValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation->pred-maps   ::HybridDNFSimpleValuation [val]
  (throw (UnsupportedOperationException.)))


(comment 

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

(defmethod restrict-valuation       [::HybridDNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (let [pos (envs/get-positive-conjuncts con)
	neg (envs/get-negative-conjuncts con)]
    (make-dnf-simple-valuation 
     (filter identity (for [clause (:dnf val)] (restrict-clause clause pos neg)))
     (:bound val))))
)
