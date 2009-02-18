(in-ns 'edu.berkeley.ai.angelic)

;; More method for propositional descriptions

(derive ::PropositionalDescription ::Description)

(defmulti parse-description              (fn [desc domain params] (first desc)))
(defmulti instantiate-description-schema (fn [desc instance] (:class desc)))
(defmulti ground-description             (fn [desc var-map] (:class desc)))


; Optimal and pessimal

(defmethod parse-description :pess [desc domain params]
  (util/assert-is (= (count desc) 1))
  *pessimal-description*)

(defmethod instantiate-description-schema ::PessimalDescription [desc instance]
  desc)

(defmethod ground-description ::PessimalDescription [desc var-map]
  desc)


(defmethod parse-description :opt [desc domain params]
  (util/assert-is (<= (count desc) 2))
  (if (= (count desc) 1)
      (make-optimal-description)
    (make-optimal-description (second desc))))

(defmethod instantiate-description-schema ::ConditionalDescription [desc instance]
  desc)

(defmethod ground-description ::ConditionalDescription [desc var-map]
  (make-conditional-description 
   (envs/ground-propositional-condition (util/safe-get desc :condition) var-map)
   (util/safe-get desc :max-reward)))


(defmethod instantiate-description-schema ::IdentityDescription [desc instance]  desc)

(defmethod ground-description ::IdentityDescription [desc var-map]  desc)




(comment 
;; Vacuous descriptions


(derive ::VacuousPropositionalDescription ::PropositionalDescription)

(defmethod parse-description nil [desc domain params] (parse-description [:vac] domain params))

(defmethod parse-description :vac [desc domain params]
;  (prn (second desc))
  (util/assert-is (<= (count desc) 2))
  {:class ::VacuousPropositionalDescription :cost (second desc)})


(defmethod instantiate-description-schema ::VacuousPropositionalDescription [desc instance]
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (assoc desc :all-dnf (list (util/map-map #(vector % :unknown) (strips/get-strips-predicate-instantiations instance))))) 


(defmethod ground-description ::VacuousPropositionalDescription [desc var-map] desc)


(defmethod progress-optimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::VacuousPropositionalDescription] [val desc]
  (dsv/make-dnf-simple-valuation (:all-dnf desc) (if-let [c (:cost desc)] (+ c (:bound val)) Double/POSITIVE_INFINITY)))


(defmethod progress-pessimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::VacuousPropositionalDescription] [val desc]
  (dsv/make-dnf-simple-valuation nil (if-let [c (:cost desc)] (+ c (:bound val)) Double/NEGATIVE_INFINITY))) 
 )




