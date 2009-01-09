(in-ns 'edu.berkeley.ai.angelic)

(defmulti parse-description              (fn [desc domain params] (first desc)))
(defmulti instantiate-description-schema (fn [desc instance] (:class desc)))
(defmulti ground-description             (fn [desc var-map] (:class desc)))


(defmulti progress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti progress-pessimistic (fn [val desc] [(:class val) (:class desc)]))

(defmulti regress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti regress-pessimistic (fn [val desc] [(:class val) (:class desc)]))



; Default - some nice vacuous descriptions

(defmethod parse-description nil [desc domain params]
  (parse-description [:vac] domain params))

(defmethod parse-description :vac [desc domain params]
;  (prn (second desc))
  (assert-is (<= (count desc) 2))
  {:class ::VacuousDescription :cost (second desc)})

(defmethod instantiate-description-schema ::VacuousDescription [desc instance]
  (assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (assoc desc :all-dnf (list (map-map #(vector % :unknown) (edu.berkeley.ai.domains.strips/get-ground-atoms instance))))) 

(defmethod ground-description ::VacuousDescription [desc var-map]
  desc)


(defmethod progress-optimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::VacuousDescription] [val desc]
  (edu.berkeley.ai.angelic.dnf-simple-valuations/make-dnf-simple-valuation (:all-dnf desc) (if-let [c (:cost desc)] (+ c (:bound val)) Double/POSITIVE_INFINITY)))

(defmethod progress-pessimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::VacuousDescription] [val desc]
  (edu.berkeley.ai.angelic.dnf-simple-valuations/make-dnf-simple-valuation nil (if-let [c (:cost desc)] (+ c (:bound val)) Double/NEGATIVE_INFINITY))) 