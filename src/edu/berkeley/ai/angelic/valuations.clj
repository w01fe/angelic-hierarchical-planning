(in-ns 'edu.berkeley.ai.angelic)

(defmulti state->valuation (fn [type state] type))

(defmulti get-valuation-lower-bound :class)
(defmulti get-valuation-upper-bound :class)

(defmulti empty-valuation? :class)
(defmethod empty-valuation? :default [val]
  (= Double/NEGATIVE_INFINITY (get-valuation-lower-bound val)))

(defmulti restrict-valuation (fn [val condition] [(:class val) (:class condition)]))

(defmulti explicit-valuation-map :class)

(defmulti #^{:doc "Get a (hopefully canonical), possibly implicit representation of the state set, ignoring predicates in subsumption-map, plus an auxillary representation of this remaining information with use of valuation-subsumes"}
          get-valuation-states (fn [val subsumption-map] (:class val)))

(defmulti #^{:doc "Does val1 subsume val2, given that they have identical get-valuation-states under subsumption-map"}
          valuation-subsumes? (fn [val1 val2 subsumption-map] [(:class val1) (:class val2)]))

(defmulti #^{:doc "Get a state consistent with this valuation, or nil if none"}
          extract-a-state :class)

(defmulti #^{:doc "Intersect these valuations, keeping the reward part from the first."}
          intersect-valuations (fn [v1 v2] [(:class v1) (:class v2)]))

(defmulti #^{:doc "Like intersect-valuations, but returns a non-empty subset of the intersection as quickly as possible."}
          sub-intersect-valuations (fn [v1 v2] [(:class v1) (:class v2)]))


(def *no-subsumption-info* {:class ::NoSubsumptionInfo})

(defmethod valuation-subsumes?     [::NoSubsumptionInfo ::NoSubsumptionInfo] [val1 val2 subsumption-map]
  true
  )

(defmethod get-valuation-states ::Valuation [val subsumption-map]
  (util/assert-is (empty? subsumption-map))
  [(.keySet (explicit-valuation-map val)) *no-subsumption-info*])

(defmethod extract-a-state ::Valuation [val]
  (first (keys (explicit-valuation-map val))))


;; Endpoint Valuations



(derive ::PessimalValuation ::Valuation)

(def *pessimal-valuation* {:class ::PessimalValuation})

(defmethod get-valuation-lower-bound ::PessimalValuation [val] Double/NEGATIVE_INFINITY)
(defmethod get-valuation-upper-bound ::PessimalValuation [val] Double/NEGATIVE_INFINITY)
(defmethod restrict-valuation [::PessimalValuation :edu.berkeley.ai.envs/Condition] [val cond] val)
(defmethod explicit-valuation-map ::PessimalValuation [val] {})
(defmethod get-valuation-states ::PessimalValuation [val subsumption-map] [nil *no-subsumption-info*])




(defstruct conditional-valuation :class :condition :max-reward)

(derive ::ConditionValuation ::Valuation)

(defn make-conditional-valuation 
  [condition max-reward]
;  (prn condition max-reward)
  (if (and (envs/consistent-condition? condition) (> max-reward Double/NEGATIVE_INFINITY))
      (struct conditional-valuation ::ConditionalValuation condition max-reward)
    *pessimal-valuation*))

(defn make-optimal-valuation  
  ([] (make-optimal-valuation Double/POSITIVE_INFINITY))
  ([max-reward] (make-conditional-valuation envs/*true-condition* max-reward)))


(defmethod get-valuation-lower-bound ::ConditionalValuation [val] 
  Double/NEGATIVE_INFINITY)

(defmethod get-valuation-upper-bound ::ConditionalValuation [val] 
  (:max-reward val))

(defmethod restrict-valuation [::ConditionalValuation :edu.berkeley.ai.envs/Condition] 
  [val cond]
  (make-conditional-valuation 
   (envs/conjoin-conditions (:condition val) cond) 
   (:max-reward val)))

(defmethod empty-valuation? ::ConditionalValuation [val] false)

;(defmethod explicit-valuation-map ::ConditionalValuation [val] {})

(defmethod get-valuation-states ::ConditionalValuation [val subsumption-map] [(gensym) nil])



;; Explicit valuations

(defstruct explicit-valuation :class :state-map)

(derive ::ExplicitValuation ::Valuation)

(defn- make-explicit-valuation- [state-map]
;  (if (empty? state-map)
;      *pessimal-valuation*
    (struct explicit-valuation ::ExplicitValuation state-map));)

(defn make-explicit-valuation [state-value-pairs]
  (make-explicit-valuation- 
   (reduce (fn [map [state value]] 
	     (if (> value (or (get map state) Double/NEGATIVE_INFINITY))
	       (assoc map state value)
	       map))
	   {} state-value-pairs)))

(defmethod state->valuation ::ExplicitValuation [type state]
  (make-explicit-valuation [[state 0]]))

(defmethod get-valuation-lower-bound ::ExplicitValuation [val]
  (if-let [v (vals (:state-map val))]
      (reduce min v)
    Double/NEGATIVE_INFINITY))

(defmethod get-valuation-upper-bound ::ExplicitValuation [val]
  (reduce max (cons Double/NEGATIVE_INFINITY (vals (:state-map val)))))

(defmethod empty-valuation? ::ExplicitValuation [val]
  (empty? (:state-map val)))

(defmethod restrict-valuation [::ExplicitValuation :edu.berkeley.ai.envs/Condition]
  [val condition]
  (make-explicit-valuation- 
   (reduce (fn [m k] (if (envs/satisfies-condition? k condition) 
		         m
		       (dissoc m k)))
	   (:state-map val) (keys (:state-map val)))))
;(into {} (filter (fn [[k v]] (envs/satisfies-condition? k condition)) (:state-map val)))))

(defmethod explicit-valuation-map ::ExplicitValuation [val]
  (:state-map val))


