(in-ns 'edu.berkeley.ai.angelic)

;; Methods for descriptions

(defmulti progress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti progress-pessimistic (fn [val desc] [(:class val) (:class desc)]))

(defmulti regress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti regress-pessimistic (fn [val desc] [(:class val) (:class desc)]))



;; Explicit descriptions

(defstruct explicit-description :class :action-space)

(derive ::ExplicitDescription ::Description)

(defn make-explicit-description [action-space]
  (struct explicit-description ::ExplicitDescription action-space))

(defn progress-explicit [val desc]
  (make-explicit-valuation ; handles reduction
;    (util/merge-reduce min {}
   (for [[state reward] (explicit-valuation-map val)
	 action (envs/applicable-actions state (:action-space desc))]
     (let [[next step-reward] (envs/next-state-and-reward state action)]
       [next (+ reward step-reward)])))) ;)

(defmethod progress-optimistic [::Valuation ::ExplicitDescription]  [val desc]
;  (prn "po")
  (progress-explicit val desc))

(defmethod progress-pessimistic [::Valuation ::ExplicitDescription]  [val desc]
;  (prn "pp")
  (progress-explicit val desc))


;; Endpoint descriptions

(derive ::PessimalDescription ::Description)
(def *pessimal-description* {:class ::PessimalDescription})

(defmethod progress-optimistic [::Valuation ::PessimalDescription] [val desc]
  *pessimal-valuation*)

(defmethod progress-pessimistic [::Valuation ::PessimalDescription] [val desc]
  *pessimal-valuation*)

(defmethod progress-optimistic [::PessimalValuation ::Description] [val desc]
  *pessimal-valuation*)

(defmethod progress-pessimistic [::PessimalValuation ::Description] [val desc]
  *pessimal-valuation*)

(prefer-method progress-optimistic [::Valuation ::PessimalDescription] [::PessimalValuation ::Description])
(prefer-method progress-pessimistic [::Valuation ::PessimalDescription] [::PessimalValuation ::Description])


(defstruct conditional-description :class :condition :max-reward)
(derive ::ConditionalDescription ::Description)
(defn make-conditional-description [condition max-reward]
  (if (or (= condition envs/*false-condition*)
	  (= max-reward Double/NEGATIVE_INFINITY))
      *pessimal-description*
    (struct conditional-description ::ConditionalDescription condition max-reward)))

(defn make-optimal-description
  ([] (make-optimal-description Double/POSITIVE_INFINITY))
  ([opt-rew] (make-conditional-description envs/*true-condition* opt-rew)))

(defmethod progress-optimistic [::PessimalValuation ::ConditionalDescription] [val desc]
  val)

(defmethod progress-optimistic [::Valuation ::ConditionalDescription] [val desc]
  (make-conditional-valuation 
   (:condition desc) 
   (+ (:max-reward desc)
      (get-valuation-upper-bound val))))

(defmethod progress-pessimistic [::Valuation ::ConditionalDescription] [val desc]
  (throw (UnsupportedOperationException.)))


(derive ::IdentityDescription ::Description)
(def *identity-description* {:class ::IdentityDescription})
(defmethod progress-optimistic [::Valuation ::IdentityDescription] [val desc] val)
(defmethod progress-pessimistic [::Valuation ::IdentityDescription] [val desc] val)



  