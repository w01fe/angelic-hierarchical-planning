(ns edu.berkeley.ai.angelic.hybrid-dnf-simple-valuations
  (:use [edu.berkeley.ai.angelic :as angelic])
  (:import [java.util HashMap])
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


;; Hierarchical preconditions for use with this sort of valuation
;(derive ::HybridHierarchicalPrecondition ::envs/Conddition
(defstruct hybrid-hierarchical-precondition :pos :neg :var-const :var-form :form-form :form-const)

(defn make-hybrid-hierarchical-precondition [pos neg var-const var-form form-form form-const]
  (struct hybrid-hierarchical-precondition pos neg var-const var-form form-form form-const))

(def *true-hhp* (make-hybrid-hierarchical-precondition nil nil nil nil nil nil))

(defn conjoin-hybrid-hierarchical-preconditions [h1 h2]
  (cond (= h1 *true-hhp*) h2
	(= h2 *true-hhp*) h1
	:else             (merge-with concat h1 h2)))

(let [types 
      [[::hybrid/NumVar ::hybrid/NumConst]
       [::hybrid/NumVar ::hybrid/NumForm]
       [::hybrid/NumForm ::hybrid/NumForm]
       [::hybrid/NumForm ::hybrid/NumConst]]]
  (defn extract-hybrid-hierarchical-precondition [pos neg num var-map constant-numeric-functions numeric-vals]
    (let [diffs (hybrid/extract-difference-constraints num var-map constant-numeric-functions numeric-vals)
	  cdiffs (util/group-by #(vector (:class (:left %)) (:class (:right %))) diffs)]
      (util/assert-is (empty? (util/difference-coll (util/keyset types) types)))
      (apply make-hybrid-hierarchical-precondition 
	     (map #(props/simplify-atom var-map %) pos)
	     (map #(props/simplify-atom var-map %) neg)
	     (map cdiffs types)))))

;; TODO: change to dish out
(defn split-and-var-translate-hhp [con var-pos-map expansion-len]
  (let [{:keys [pos neg var-form form-form form-const]} con
	ret (vec (cons (make-hybrid-hierarchical-precondition 
			pos neg nil nil form-form form-const) 
		       (repeat (dec expansion-len) *true-hhp*)))]
    (reduce (fn [ret vf]
	      (let [var (util/safe-get vf :var)
		    [ind nv] (util/safe-get var-pos-map var)]
		(assoc ret ind
		       (util/assoc-cons (nth ret ind)
			  :var-form (hybrid/make-numeric-var nv)))))
	    var-form)))


(defn restrict-var-map [val con var-map]
  "Perform inference the opposite way of restrict-valuation."
  ;; TODO!!
  )


;; TODO!!
(defmethod restrict-valuation       [::HybridDNFSimpleValuation :edu.berkeley.ai.envs/ConjunctiveCondition] [val con]
  (throw (UnsupportedOperationException.))) 
  
(defmethod explicit-valuation-map ::HybridDNFSimpleValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod get-valuation-states   ::HybridDNFSimpleValuation [val]
  (throw (UnsupportedOperationException.)))

(defmethod valuation->pred-maps   ::HybridDNFSimpleValuation [val]
  (for [clause (util/safe-get val :clauses)]
    (let [true-map (HashMap.) poss-map (HashMap.)]
      (doseq [[#^clojure.lang.APersistentVector pred stat] (util/safe-get clause :conj)]
	(let [#^HashMap m (if (= stat :true) true-map poss-map)
	      pred-name (.get pred 0)]
	  (.put m pred-name (cons pred (.get m pred-name)))))
      [true-map poss-map])));)


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
