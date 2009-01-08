(in-ns 'edu.berkeley.ai.envs)

; ::Condition

(defmulti satisfies-condition? (fn [state condition] (:class condition)))


(derive ::SimpleCondition ::Condition)

(defstruct simple-condition :class :test)

(defn make-simple-condition [test]
  (struct simple-condition ::SimpleCondition test))

(defmethod satisfies-condition? ::SimpleCondition [state condition]
  ((:test condition) state))




