(in-ns 'edu.berkeley.ai.angelic)

(defmulti parse-description              (fn [desc domain params] (first desc)))
(defmulti instantiate-description-schema (fn [desc instance] (:class desc)))
(defmulti ground-description             (fn [desc var-map] (:class desc)))


(defmulti progress-optimistic (partial map :class))
(defmulti progress-pessimistic (partial map :class))

(defmulti regress-optimistic (partial map :class))
(defmulti regress-pessimistic (partial map :class))



; Default - some nice vacuous descriptions

(defmethod parse-description nil [desc domain params]
  (parse-description [:vac] domain))

(defmethod parse-description :vac [desc domain params]
  (assert-is (<= (count desc) 2))
  {:class ::VacuousDescription :cost (second desc)})

(defmethod instantiate-description-schema ::VacuousDescription [desc instance]
  (assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (assoc desc :all-dnf (map-map #(vector % :unknown) (edu.berkeley.ai.domains.strips/get-ground-atoms instance)))) 

(defmethod ground-description ::VacuousDescription [desc var-map]
  desc)


(defmethod progress-optimistic [::VacuousDescription ::DNFSimpleValuation] [desc val]
  (make-dnf-simple-valuation (:all-dnf desc) (if-let [c (:cost desc)] (+ c (:bound val)) Double/POSITIVE_INFINITY)))

(defmethod progress-pessimistic [::VacuousDescription ::DNFSimpleValuation] [desc val]
  (make-dnf-simple-valuation nil (if-let [c (:cost desc)] (+ c (:bound val)) Double/NEGATIVE_INFINITY))) 