(ns edu.berkeley.ai.util.hybrid-constraints
  (:use clojure.test  edu.berkeley.ai.util  )
  (:require [edu.berkeley.ai.util [propositions :as props] [intervals :as iv]
	     [hybrid :as hybrid] [linear-expressions :as le]]
	    ))

;; Here, we assume a hybrid state is a [discrete-atom-set numeric-val-map] pair.

(defmulti evaluate-constraint (fn [constraint var-map objects [discrete-atoms numeric-vals]] (:class constraint))) 
(defmulti split-constraint (fn [constraint var-map objects] (:class constraint)))
  ; Get [pos-atoms neg-atoms only-numeric-constraint]
(defmulti get-numeric-yield (fn [constraint var-map objects [discrete-atoms numeric-vals]] (:class constraint)))
  ; Get nil (false) or a possibly-empty list of numeric constraints, where the :left is a single ::NumVar expression.


; Idea: left - right = diff, diff is a number, left may be a var or form, right must be a form or constant .
; This is the restricted form of numeric constraint allowed in hybrid-strips-hierarchies for now.
(defstruct hybrid-strips-difference-constraint :pred :left :right :diff)
(defn make-hybrid-strips-difference-constraint [pred left right diff]
  (struct hybrid-strips-difference-constraint pred left right diff))

(defmulti extract-difference-constraints (fn [constraint var-map constant-numeric-functions numeric-vals] (:class constraint)))

;; Extract a set of difference constraints


(derive ::NumConstraint ::Constraint)
(defstruct hybrid-strips-numeric-constraint :class :pred :left :right)
(defn make-numeric-constraint [pred left right]
  (struct hybrid-strips-numeric-constraint ::NumConstraint pred left right))

(defmethod evaluate-constraint ::NumConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  ((:pred constraint)
   (le/evaluate-numeric-expr (:left constraint) var-map numeric-vals)
   (le/evaluate-numeric-expr (:right constraint) var-map numeric-vals)))

(defmethod split-constraint ::NumConstraint [constraint var-map objects]
  [nil nil constraint])

;; TODO: abstraction violation.
(defmethod get-numeric-yield ::NumConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (if (isa? (:class (:left constraint)) ::le/NumVar) 
      [(make-numeric-constraint (:pred constraint) (:left constraint) 
	 (le/make-numeric-constant (le/evaluate-numeric-expr (:right constraint) var-map numeric-vals)))]
    (when (evaluate-constraint constraint var-map objects [discrete-atoms numeric-vals]) [])))

;; TODO: abstraction violations.
(defmethod extract-difference-constraints ::NumConstraint 
  [constraint var-map constant-numeric-functions numeric-vals] 
  (let [{:keys [pred left right]} constraint
	left  (le/ground-and-simplify-numeric-expr left var-map constant-numeric-functions numeric-vals)
	right (le/ground-and-simplify-numeric-expr right var-map constant-numeric-functions numeric-vals)]
    (assert-is (contains? #{::le/NumVar ::le/NumForm} (:class left)))
    (apply make-hybrid-strips-difference-constraint 
	   pred 
	   left
	   (le/extract-numeric-expr-form-and-diff right))))					




(derive ::DiscPosConstraint ::Constraint)
(defstruct hybrid-strips-discrete-pos-constraint :class :atom)
(defn make-discrete-pos-constraint [atom]
  (struct hybrid-strips-discrete-pos-constraint ::DiscPosConstraint atom))

(defmethod evaluate-constraint ::DiscPosConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint))))

(defmethod split-constraint ::DiscPosConstraint [constraint var-map objects]
  [[(props/simplify-atom var-map (:atom constraint))] nil nil])


(derive ::DiscNegConstraint ::Constraint)
(defstruct hybrid-strips-discrete-neg-constraint :class :atom)
(defn make-discrete-neg-constraint [atom]
  (struct hybrid-strips-discrete-neg-constraint ::DiscNegConstraint atom))

(defmethod evaluate-constraint ::DiscNegConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (not (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint)))))

(defmethod split-constraint ::DiscNegConstraint [constraint var-map objects]
  [nil [(props/simplify-atom var-map (:atom constraint))] nil])



(derive ::ConjunctiveConstraint ::Constraint)
(defstruct hybrid-strips-conjuntive-constraint :class :constraints)
(defn make-conjunctive-constraint [constraints]
  (struct hybrid-strips-conjuntive-constraint ::ConjunctiveConstraint constraints))

(defmethod evaluate-constraint ::ConjunctiveConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
;  (doseq [x (:constraints constraint)] (println x (evaluate-constraint x var-map objects [discrete-atoms numeric-vals])))
  (every? #(evaluate-constraint % var-map objects [discrete-atoms numeric-vals]) (:constraints constraint)))

(defmethod split-constraint ::ConjunctiveConstraint [constraint var-map objects]
  (let [bits (map #(split-constraint % var-map objects) (:constraints constraint))]
    [(apply concat (map first bits))
     (apply concat (map second bits))
     (make-conjunctive-constraint (filter identity (map #(nth % 2) bits)))]))

(defmethod get-numeric-yield ::ConjunctiveConstraint  [constraint var-map objects [discrete-atoms numeric-vals]]
  (loop [constraints (seq (:constraints constraint)) yield []]
    (if constraints
        (when-let [c (get-numeric-yield (first constraints) var-map objects [discrete-atoms numeric-vals])]
	  (recur (next constraints) (into yield c)))
      yield)))

(defmethod extract-difference-constraints ::ConjunctiveConstraint [constraint var-map constant-numeric-functions numeric-vals] 
  (apply concat (map #(extract-difference-constraints % var-map constant-numeric-functions numeric-vals) (:constraints constraint))))



(derive ::ForallConstraint ::Constraint)
(defstruct hybrid-strips-forall-constraint :class :vars :condition :yield)
(defn make-forall-constraint [vars condition yield]
  (struct hybrid-strips-forall-constraint ::ForallConstraint vars condition yield))

(defmethod evaluate-constraint ::ForallConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (every? (fn [full-var-map] 
;	    (println full-var-map)
	    (or (not (evaluate-constraint (:condition constraint) full-var-map objects [discrete-atoms numeric-vals]))
		(evaluate-constraint (:yield constraint) full-var-map objects [discrete-atoms numeric-vals])))
	  (let [vars (seq (:vars constraint))]
	    (for [combo (apply cartesian-product (map #(get objects (first %)) vars))]
	      (into var-map (map (fn [val tv] [(second tv) val]) combo vars))))))

(defmethod split-constraint ::ForallConstraint [constraint var-map objects]
;  (println (:condition constraint) (isa? (:class constraint) ::ConjunctiveConstraint))
  (if (or (empty? (:condition constraint))
	  (and (isa? (:class (:condition constraint)) ::ConjunctiveConstraint)
	       (empty? (safe-get (:condition constraint) :constraints))))
      (let [var-maps
	     (let [vars (seq (:vars constraint))]
	       (for [combo (apply cartesian-product (map #(get objects (first %)) vars))]
		 (into var-map (map (fn [val tv] [(second tv) val]) combo vars))))
	    bits (map #(split-constraint (:yield constraint) % objects) var-maps)]
;;	(println "EMPTY")
	[(apply concat (map first bits))
	 (apply concat (map second bits))
	 (make-conjunctive-constraint (filter identity (map #(nth % 2) bits)))])
    [nil nil constraint]))

(defmethod get-numeric-yield ::ForallConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (let [consistent-var-maps
        (filter #(evaluate-constraint (:condition constraint) % objects [discrete-atoms numeric-vals])
          (let [vars (seq (:vars constraint))]
	    (for [combo (apply cartesian-product (map #(get objects (first %)) vars))]
	      (into var-map (map (fn [val tv] [(second tv) val]) combo vars)))))]
    (loop [var-maps (seq consistent-var-maps) yield []]
      (if var-maps
        (when-let [c (get-numeric-yield (:yield constraint) (first var-maps) objects [discrete-atoms numeric-vals])]
	  (recur (next var-maps) (into yield c)))
	yield))))


(def *true-constraint* (make-conjunctive-constraint nil))


(declare parse-and-check-constraint)
(defn parse-and-check-nonconjunctive-constraint [constraint discrete-vars predicates numeric-vars numeric-functions only-atomic-var?]
  (let [[f & r] constraint]
    (cond (and (= f 'not) (contains? predicates (ffirst r)))
	    (make-discrete-neg-constraint (hybrid/check-hybrid-atom (second constraint) predicates discrete-vars))
          (contains? predicates f)
	    (make-discrete-pos-constraint (hybrid/check-hybrid-atom constraint predicates discrete-vars))
	  (= f 'forall)
	    (do (let [vars (props/parse-typed-pddl-list (nth constraint 1))
		      all-discrete (into discrete-vars (map (fn [[t v]] [v t]) vars))]
		  (assert-is (= (count all-discrete) (+ (count vars) (count discrete-vars))))
		  (make-forall-constraint
		   vars
		   (parse-and-check-constraint (nth constraint 2) all-discrete predicates 
					       (when-not only-atomic-var? numeric-vars)
					       numeric-functions only-atomic-var?)
		   (parse-and-check-constraint (nth constraint 3) all-discrete predicates 
					       numeric-vars 
					       numeric-functions only-atomic-var?))))
	  :else
	    (do (assert-is (= (count constraint) 3) "%s" constraint)
		(make-numeric-constraint 
		 (safe-get {'= = '< < '> > '<= <= '>= >=} f)
		 (le/parse-and-check-numeric-expression (nth constraint 1)
		   discrete-vars numeric-vars numeric-functions true)
		 (le/parse-and-check-numeric-expression (nth constraint 2)
		   discrete-vars  (when-not only-atomic-var? numeric-vars)
		   numeric-functions))))))
		      
(defn parse-and-check-constraint 
  ([constraint discrete-vars predicates numeric-vars numeric-functions]
     (parse-and-check-constraint constraint discrete-vars predicates numeric-vars numeric-functions false))
  ([constraint discrete-vars predicates numeric-vars numeric-functions only-atomic-var?]
;  (println constraint)
  (if (or (empty? constraint) (= (first constraint) 'and))
      (make-conjunctive-constraint 
       (doall
	(for [sub (next constraint)] 
	 (parse-and-check-nonconjunctive-constraint sub discrete-vars predicates numeric-vars numeric-functions only-atomic-var?))))
    (parse-and-check-nonconjunctive-constraint constraint discrete-vars predicates numeric-vars numeric-functions only-atomic-var?))))


(deftest constraints
  (is (evaluate-constraint (parse-and-check-constraint '(= 1 1) nil nil nil nil) nil nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(= 1 2) nil nil nil nil) nil nil [nil nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil) {'x 1 'y 1} nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil) {'x 2 'y 1} nil [nil nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(not (abc x y)) '{x xt y yt} '{abc [xt yt]} nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil])))
  (is (not (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil) 
				     '{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y2]} nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 2)) nil nil nil nil) nil nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 1)) nil nil nil nil) nil nil [nil nil])))
  (is (not (evaluate-constraint (parse-and-check-constraint '(and (= 2 1) (= 1 1)) nil nil nil nil) nil nil [nil nil])))
  (is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x2] [bar x1] [bar x2]} nil]))
  (is (not (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x3] [bar x1] [bar x2]} nil])))
  (is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
	     '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]}) 
	    '{y yv z 17} '{xt [x1 x2 x3 x4] yt [yv]} 
	    ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
	    '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
	      [froxy x1 yv] 17, [froxy x2 yv] 17, [froxy x3 yv] 19, [froxy x4 yv] 17}]))
  (is (not (evaluate-constraint 
		 (parse-and-check-constraint 
		  '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
		  '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]}) 
		 '{y yv z 17} '{xt [x1 x2 x3 x4] yt [yv]} 
		 ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
		 '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
		   [froxy x1 yv] 17, [froxy x2 yv] 16, [froxy x3 yv] 19, [froxy x4 yv] 17}]))))
  


