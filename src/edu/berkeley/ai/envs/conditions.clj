(in-ns 'edu.berkeley.ai.envs)

;;; Conditions

;; Methods

(defmulti satisfies-condition? (fn [state condition] (:class condition)))
(defmulti consistent-condition? :class)
(defmulti conjoin-conditions (fn [c1 c2] [(:class c1) (:class c2)]))
(defmulti satisfying-states (fn [condition state-space] [(:class condition) (:class state-space)]))



;; Simple conditions are just predicates on states

(derive ::SimpleCondition ::Condition)

(defstruct simple-condition :class :test :known-consistent)

(defn make-simple-condition 
  ([test] (make-simple-condition test false))
  ([test kc] (struct simple-condition ::SimpleCondition test kc)))

(defmethod satisfies-condition? ::SimpleCondition [state condition]
  ((:test condition) state))

(defmethod conjoin-conditions [::Condition ::Condition] [c1 c2]
  (if (= c1 c2) c1
    (make-simple-condition 
     #(and (satisfies-condition? % c1) (satisfies-condition? % c2)))))

(defmethod consistent-condition? ::SimpleCondition [condition] 
  (if (:known-consistent condition) 
      true
    (throw (UnsupportedOperationException. (str condition)))))

; cons

;; Trivial conditions

(derive ::FalseCondition ::SimpleCondition)
(def *false-condition* {:class ::FalseCondition :test (constantly false)})

(defmethod satisfies-condition? ::FalseCondition [state condition] false)
(defmethod consistent-condition? ::FalseCondition [condition] false)
(defmethod conjoin-conditions    [::FalseCondition ::Condition] [fc c] fc)
(defmethod conjoin-conditions    [::Condition ::FalseCondition] [c fc] fc)
(defmethod conjoin-conditions    [::FalseCondition ::FalseCondition] [fc1 fc2] fc1)
(defmethod satisfying-states     ::FalseCondition [c] nil)





;; Propositional conditions

(derive ::PropositionalCondition ::Condition)

(defmulti ground-propositional-condition (fn [cond var-map] (:class cond)))



;; Conjunctive conditions

(derive ::ConjunctiveCondition ::PropositionalCondition)

(defstruct conjunctive-condition :class :pos :neg)

(defn make-conjunctive-condition [pos neg] 
  (struct conjunctive-condition ::ConjunctiveCondition (set pos) (set neg)))

;(def *true-condition* (make-conjunctive-condition nil nil))

(defn get-positive-conjuncts [c] (util/safe-get c :pos))

(defn get-negative-conjuncts [c] (util/safe-get c :neg))


(defmethod satisfies-condition? ::ConjunctiveCondition [s c]
  (and (every?   s (:pos c))
       (not-any? s (:neg c)))) 

(defmethod conjoin-conditions [::ConjunctiveCondition ::ConjunctiveCondition] [c1 c2]
  (make-conjunctive-condition 
   (util/union (get-positive-conjuncts c1) (get-positive-conjuncts c2))
   (util/union (get-negative-conjuncts c1) (get-negative-conjuncts c2))))
			      
(defmethod ground-propositional-condition ::ConjunctiveCondition [c var-map]
  (let [simplifier #(props/simplify-atom var-map %)]
    (make-conjunctive-condition
     (map simplifier (get-positive-conjuncts c))
     (map simplifier (get-negative-conjuncts c)))))

(defmethod consistent-condition? ::ConjunctiveCondition [condition]
  (empty? (util/intersection (:pos condition) (:neg condition))))

(defn constant-simplify-condition [condition always-true always-false]
  (let [pos (:pos condition)
	neg (:neg condition)]
    (if (or (some always-true neg) (some always-false pos)) *false-condition*
      (make-conjunctive-condition
       (remove always-true pos)
       (remove always-false neg)))))



(derive ::TrueCondition ::ConjunctiveCondition)
(def *true-condition* {:class ::TrueCondition :pos nil :neg nil})

(defmethod satisfies-condition? ::TrueCondition [state condition] true)
(defmethod consistent-condition? ::TrueCondition [condition] true)
(defmethod conjoin-conditions    [::TrueCondition ::Condition] [tc c] c)
(defmethod conjoin-conditions    [::TrueCondition ::ConjunctiveCondition] [tc c] c)
(defmethod conjoin-conditions    [::Condition ::TrueCondition] [c tc] c)
(defmethod conjoin-conditions    [::ConjunctiveCondition ::TrueCondition] [c tc] c)
(defmethod conjoin-conditions    [::TrueCondition ::TrueCondition] [tc1 tc2] tc1)
(defmethod conjoin-conditions    [::TrueCondition ::FalseCondition] [tc fc] fc)
(defmethod conjoin-conditions    [::FalseCondition ::TrueCondition] [fc tc] fc)
(defmethod ground-propositional-condition ::TrueCondition [c var-map] c)



; Constraints for hybrid state spaces

(derive ::ConstraintCondition ::Condition)
(defstruct constraint-condition :class :constraint :objects :var-map)

(defn make-constraint-condition [constraint objects var-map] 
  (struct constraint-condition ::ConstraintCondition constraint objects var-map))

(defmethod satisfies-condition? ::ConstraintCondition [s c]
  (edu.berkeley.ai.util.hybrid/evaluate-constraint (:constraint c) (:var-map c) (:objects c) s))

(defmethod consistent-condition? ::ConstraintCondition [condition]
  (throw (UnsupportedOperationException.)))
