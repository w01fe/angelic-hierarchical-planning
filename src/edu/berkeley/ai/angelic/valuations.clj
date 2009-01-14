(in-ns 'edu.berkeley.ai.angelic)

(defmulti make-initial-valuation (fn [type env] type))

(defmulti get-valuation-lower-bound :class)
(defmulti get-valuation-upper-bound :class)

(defmulti empty-valuation? :class)
(defmethod empty-valuation? :default [val]
  (= Double/NEGATIVE_INFINITY (get-valuation-lower-bound val)))

(defmulti restrict-valuation (fn [val condition] [(:class val) (:class condition)]))

(defmulti explicit-valuation-map :class)



;; Explicit valuations

(defstruct explicit-valuation :class :state-map)

(derive ::ExplicitValuation ::Valuation)

(defn- make-explicit-valuation- [state-map]
  (struct explicit-valuation ::ExplicitValuation state-map))

(defn make-explicit-valuation [state-value-pairs]
  (make-explicit-valuation- 
   (reduce (fn [map [state value]] 
	     (if (> value (or (get map state) Double/NEGATIVE_INFINITY))
	       (assoc map state value)
	       map))
	   {} state-value-pairs)))


(defmethod make-initial-valuation :ExplicitValuation [type env]
  (make-explicit-valuation [(get-initial-state env) 0]))

(defmethod get-valuation-lower-bound ::ExplicitValuation [val]
  (reduce min (cons Double/NEGATIVE_INFINITY (vals (:state-map val)))))

(defmethod get-valuation-upper-bound ::ExplicitValuation [val]
  (reduce max (cons Double/NEGATIVE_INFINITY (vals (:state-map val)))))

(defmethod empty-valuation? ::ExplicitValuation [val]
  (empty? (:state-map val)))

(defmethod restrict-valuation [::ExplicitValuation :edu.berkeley.ai.envs/Condition]
  [val condition]
  (make-explicit-valuation- (into {} (filter (fn [[k v]] (satisfies-condition? k condition)) (:state-map val)))))

(defmethod explicit-valuation-map ::ExplicitValuation [val]
  (:state-map val))



;; Endpoint Valuations



(derive ::PessimalValuation ::Valuation)

(def *pessimal-valuation* (struct pessimal-valuation ::PessimalValuation))

(defmethod get-valuation-lower-bound ::PessimalValuation [val] Double/NEGATIVE_INFINITY)
(defmethod get-valuation-upper-bound ::PessimalValuation [val] Double/NEGATIVE_INFINITY)
(defmethod restrict-valuation [::PessimalValuation :edu.berkeley.ai.envs/Condition] [val cond] val)
(defmethod explicit-valuation-map ::PessimalValuation [val] {})




(defstruct conditional-valuation :class :condition :max-reward)

(derive ::ConditionValuation ::Valuation)

(defn make-conditional-valuation 
  [condition max-reward]
  (if (and (consistent-condition? condition) (> max-reward Double/NEGATIVE_INFINITY))
      (struct conditional-valuation ::ConditionalValuation condition max-reward)
    *pessimal-valuation*))

(defn make-optimal-valuation  
  ([] (make-optimal-valuation Double/POSITIVE_INFINITY))
  ([max-reward] (make-conditional-valuation *true-condition* max-reward)))


(defmethod get-valuation-lower-bound ::ConditionalValuation [val] 
  Double/NEGATIVE_INFINITY)

(defmethod get-valuation-upper-bound ::ConditionalValuation [val] 
  (:max-reward val))

(defmethod restrict-valuation [::ConditionalValuation :edu.berkeley.ai.envs/Condition] 
  [val cond]
  (make-conditional-valuation 
   (conjoin-conditions (:condition val) cond) 
   (:max-reward val)))

(defmethod empty-valuation? ::ConditionalValuation [val] false)

;(defmethod explicit-valuation-map ::ConditionalValuation [val] {})


