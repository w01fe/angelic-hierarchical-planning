(in-ns 'edu.berkeley.ai.angelic)

(defmulti make-initial-valuation (fn [type env] type))

(defmulti get-valuation-lower-bound :class)
(defmulti get-valuation-upper-bound :class)
(defmulti dead-end-valuation? :class)

(defmulti restrict-valuation (fn [val condition] [(:class val) (:class condition)]))

(defmulti get-explicit-valuation :class)



;; Explicit valuations

(defstruct explicit-valuation :class :state-map)

(defn make-explicit-valuation [state-value-pairs]
  (struct explicit-valuation 
    ::ExplicitValuation
    (reduce (fn [map [state value]] 
	      (if (> value (or (get map state) Double/NEGATIVE_INFINITY))
	        (assoc map state value)
		map))
	    {} state-value-pairs)))


(defmethod make-initial-valuation :ExplicitValuation [type env]
  (make-explicit-valuation [(get-initial-state env) 0]))

(defmethod get-valuation-lower-bound ::ExplicitValuation [val]
  (reduce min (vals (:state-map val))))

(defmethod get-valuation-upper-bound ::ExplicitValuation [val]
  (reduce max (vals (:state-map val))))

(defmethod dead-end-valuation ::ExplicitValuation [val]
  (empty? (:state-map val)))

(defmethod restrict-valuation ::ExplicitValuation [val condition]
  (make-explicit-valuation (filter (fn [[k v]] (satisfies-condition? k condition)) (:state-map val))))

(defmethod get-explicit-valuation ::ExplicitValuation [val]
  val)

