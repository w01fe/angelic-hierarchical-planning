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
  (make-explicit-valuation
    (merge-reduce min {}
      (for [[state reward] (explicit-valuation-map val)
	    action (applicable-actions state (:action-space desc))]
	(let [[next step-reward] (next-state-and-reward state action)]
	  [next (+ reward step-reward)])))))

(defn progress-optimistic [::Valuation ::ExplicitDescription]  [val desc]
  (progress-explicit val desc))

(defn progress-pessimistic [::Valuation ::ExplicitDescription]  [val desc]
  (progress-explicit val desc))


;; Vacuous descriptions


(derive ::VacuousDescription ::Description)

(defmethod parse-description nil [desc domain params] 
  (parse-description [:vac] domain params))

(defmethod parse-description :vac [desc domain params]
  (assert-is (<= (count desc) 2))
  {:class ::VacuousDescription :cost (second desc)})

(defmethod progress-optimistic [::Valuation ::VacuousDescription] [val desc]
  (make-optimal-valuation 
   (if-let [c (:cost desc)] (+ c (:bound val)) Double/POSITIVE_INFINITY)))

(defmethod progress-pessimistic [::Valuation ::VacuousDescription] [val desc]
  *pessimal-valuation*)


  