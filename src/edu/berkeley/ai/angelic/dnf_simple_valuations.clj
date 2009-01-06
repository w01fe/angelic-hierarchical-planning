(in-ns 'edu.berkeley.ai.angelic)

(defstruct dnf-simple-valuation :class :dnf :bound)

; dnf clauses are maps from vars to :true or :unknown  (not present = :false)

(defn make-dnf-simple-valuation [dnf bound]
  (if-let [dnf (seq dnf)]
      (struct dnf-simple-valuation ::DNFSimpleValuation dnf bound)
    (struct dnf-simple-valuation ::DNFSimpleValuation nil Double/NEGATIVE_INFINITY)))
  
(defmethod get-valuation-lower-bound ::DNFSimpleValuation [val] (:bound val))
(defmethod get-valuation-upper-bound ::DNFSimpleValuation [val] (:bound val))
(defmethod dead-end-valuation?       ::DNFSimpleValuation [val] (:dnf val))


(defmethod restrict-valuation       [::DNFSimpleValuation ::ConjunctiveCondition] [val con]
  (make-dnf-simple-valuation 
   (filter identity
     (for [clause (:dnf val)]
       (loop [con con clause clause]
	 (cond (empty? con) clause
	       (contains? clause (first con)) (recur (rest con) (assoc clause (first con) :true))
	       :else nil))))
   (:bound val)))
