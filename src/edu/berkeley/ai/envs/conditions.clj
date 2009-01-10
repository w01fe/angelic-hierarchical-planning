(in-ns 'edu.berkeley.ai.envs)

;;; Conditions

;; Methods

(defmulti satisfies-condition? (fn [state condition] (:class condition)))
(defmulti conjoin-conditions (fn [c1 c2] [(:class c1) (:class c2)]))
(defmulti satisfying-states (fn [condition state-space] [(:class condition) (:class state-space)]))


;; Simple conditions are just predicates on states

(derive ::SimpleCondition ::Condition)

(defstruct simple-condition :class :test)

(defn make-simple-condition [test]
  (struct simple-condition ::SimpleCondition test))

(defmethod satisfies-condition? ::SimpleCondition [state condition]
  ((:test condition) state))

(defmethod conjoin-conditions [::Condition ::Condition] [c1 c2]
  (make-simple-condition 
   #(and (satisfies-condition? % c1) (satisfies-condition? % c2))))

(def *true-condition* (make-simple-condition (constantly true)))
(def *false-condition* (make-simple-condition (constantly false)))


;; Propositional conditions

(derive ::PropositionalCondition ::Condition)

(defmulti ground-propositional-condition (fn [cond var-map] (:class cond)))



;; Conjunctive conditions

(derive ::ConjunctiveCondition ::PropositionalCondition)

(defstruct conjunctive-condition :class :pos :neg)

(defn make-conjunctive-condition [pos neg] 
  (struct conjunctive-condition ::ConjunctiveCondition (set pos) (set neg)))

(defn get-positive-conjuncts [c] (safe-get c :pos))

(defn get-negative-conjuncts [c] (safe-get c :neg))


(defmethod satisfies-condition? ::ConjunctiveCondition [s c]
  (and (every?   s (:pos c))
       (not-any? s (:neg c)))) 

(defmethod conjoin-conditions [::ConjunctiveCondition ::ConjunctiveCondition] [c1 c2]
  (make-conjunctive-condition 
   (clojure.set/union (get-positive-conjuncts c1) (get-positive-conjuncts c2))
   (clojure.set/union (get-negative-conjuncts c1) (get-negative-conjuncts c2))))
			      
(defmethod ground-propositional-condition ::ConjunctiveCondition [c var-map]
  (make-conjunctive-condition
   (map (partial simplify-atom var-map) (get-positive-conjuncts c))
   (map (partial simplify-atom var-map) (get-negative-conjuncts c))))


