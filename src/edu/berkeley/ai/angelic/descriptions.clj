(in-ns 'edu.berkeley.ai.angelic)

(defmulti parse-description (fn [type desc env] type))
(defmulti instantiate-description-schema (fn [x m] (:class x)))

(defmulti progress-optimistic (partial map :class))
(defmulti progress-pessimistic (partial map :class))

(defmulti regress-optimistic (partial map :class))
(defmulti regress-pessimistic (partial map :class))
