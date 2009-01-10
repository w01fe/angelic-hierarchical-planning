(in-ns 'edu.berkeley.ai.envs)

; ::Condition

(defmulti satisfies-condition? (fn [state condition] (:class condition)))


(derive ::SimpleCondition ::Condition)

(defstruct simple-condition :class :test)

(defn make-simple-condition [test]
  (struct simple-condition ::SimpleCondition test))

(defmethod satisfies-condition? ::SimpleCondition [state condition]
  ((:test condition) state))


(defmulti conjoin-conditions (fn [c1 c2] [(:class c1) (:class c2)]))

(defmethod conjoin-conditions [::Condition ::Condition] [c1 c2]
  (make-simple-condition 
   #(and (satisfies-condition? % c1) (satisfies-condition? % c2))))


(defmulti satisfying-states (fn [condition state-space] [(:class condition) (:class state-space)]))



(def *true-condition* (make-simple-condition (constantly true)))
(def *false-condition* (make-simple-condition (constantly false)))
