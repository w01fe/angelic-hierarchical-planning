(ns edu.berkeley.ai.util.hybrid
  (:use clojure.test  edu.berkeley.ai.util)
  (:require [edu.berkeley.ai.util [propositions :as props]]))


;;; Helper types for expressions, assignments, and conditions

(defn split-var-maps [vars discrete-types numeric-types]
  (map (fn [vars] (into {} (map (fn [[t v]] [v t]) vars)))
	     (separate 
	      (fn [[t v]] 
		(cond (contains? discrete-types t) true
		      (contains? numeric-types t)  false
		      :else (throw (IllegalArgumentException.))))
	      vars)))

;; Helper

(defn check-hybrid-atom [atom arg-map var-types]
;  (println atom arg-map var-types)
  (let [args (safe-get arg-map (first atom))
	body (next atom)]
    (assert-is (= (count body) (count args)))
    (doseq [[v t] (map vector body args)]
      (assert-is (= t (get var-types v)) "%s %s %s" atom args var-types))
    (vec atom)))

;; Expressions

(defmulti evaluate-numeric-expr (fn [expr var-map numeric-vals] (:class expr))) 

(defmulti ground-and-simplify-numeric-expr (fn [expr var-map constant-numeric-fns numeric-vals] (:class expr)))
(defmulti extract-numeric-expr-form-and-diff (fn [expr] (:class expr)))  
;(defmulti translate-numeric-expr-vars (fn [expr var-map] (:class expr))) 

(defmethod ground-and-simplify-numeric-expr   ::Num [expr var-map constant-numeric-fns numeric-vals] expr)

(defmethod extract-numeric-expr-form-and-diff ::Num [expr]         (throw (UnsupportedOperationException.)))

;(defmethod translate-numeric-expr-vars        ::Num [expr var-map] expr) 


;; A constant.
(derive ::NumConst ::Num)
(defstruct hybrid-strips-numeric-constant :class :constant)
(defn make-numeric-constant [constant]
;  (assert-is (number? constant))
  (struct hybrid-strips-numeric-constant ::NumConst constant))

(defmethod evaluate-numeric-expr ::NumConst [expr var-map numeric-vals]
  (:constant expr))

;; A grounded numeric variable, .e.g., (gas)
(derive ::NumVar ::Num)
(defstruct hybrid-strips-numeric-var :class :var)
(defn make-numeric-var [var]
  (struct hybrid-strips-numeric-var ::NumVar var))

(defmethod evaluate-numeric-expr ::NumVar [expr var-map numeric-vals]
  (safe-get var-map (:var expr)))

;(defmethod translate-numeric-expr-vars        ::NumVar [expr var-map] 
;  (make-numeric-var (safe-get var-map (:var expr)))) 


; An ungrounded form, i.e., var with unfilled arguments, e.g., (distance-to ?x)
; Arguments come from discrete action arguments.
(derive ::NumForm ::Num)
(defstruct hybrid-strips-numeric-form :class :form)
(defn make-numeric-form [form]
  (struct hybrid-strips-numeric-form ::NumForm form))

(defmethod evaluate-numeric-expr ::NumForm [expr var-map numeric-vals]
  ;(println var-map)
  (safe-get numeric-vals (props/simplify-atom var-map (:form expr))))

(defmethod ground-and-simplify-numeric-expr   ::NumForm [expr var-map constant-numeric-fns numeric-vals]
  (let [form (props/simplify-atom var-map (:form expr))]
    (if (contains? constant-numeric-fns (first form))
        (make-numeric-constant (interval-point (safe-get numeric-vals form)))
      (make-numeric-form form))))

(defmethod extract-numeric-expr-form-and-diff ::NumForm [expr]         
  [expr 0])


; An expression.  Currently limited to +/- constant in some settings (i.e., effects?)
(derive ::NumExpr ::Num)
(defstruct hybrid-strips-numeric-expression :class :op :args)
(defn make-numeric-expression [op args]
  (struct hybrid-strips-numeric-expression ::NumExpr op args))

(defmethod evaluate-numeric-expr ::NumExpr [expr var-map numeric-vals]
  (apply (:op expr) (map #(evaluate-numeric-expr % var-map numeric-vals) (:args expr))))

(defmethod ground-and-simplify-numeric-expr   ::NumExpr [expr var-map constant-numeric-fns numeric-vals]
  (let [op (:op expr)
	args (map #(ground-and-simplify-numeric-expr % var-map constant-numeric-fns numeric-vals) (:args expr))]
;    (println "\nGO\n" (:args expr) "\n\n\n" args "\n\n")
    (if (every? #(isa? (:class %) ::NumConst) args)
        (make-numeric-constant (apply op (map :constant args)))
      (make-numeric-expression op args))))

(defmethod extract-numeric-expr-form-and-diff ::NumExpr [expr] 
  (let [op (:op expr)
	args (:args expr)
	[left right] args]
;    (println "ARGS" args)
    (assert-is (contains? #{+ -} op))
    (assert-is (= 2 (count args)))
    (assert-is (isa? (:class right) ::NumConst))
    (let [[e diff] (extract-numeric-expr-form-and-diff left)]
      [e (op diff (:constant right))])))

;(defmethod translate-numeric-expr-vars        ::NumExpr [expr var-map] 
;  (make-numeric-expression (:op expr) (map #(translate-numeric-expr-vars % var-map) (:args expr))))




(defn parse-and-check-numeric-expression 
  ([expr discrete-vars numeric-vars numeric-functions]
     (parse-and-check-numeric-expression expr discrete-vars numeric-vars numeric-functions false))
;  (println expr)
  ([expr discrete-vars numeric-vars numeric-functions only-atomic-var?]
  (cond (number? expr) 
          (make-numeric-constant expr)
	(contains? numeric-vars expr)
	  (make-numeric-var expr)
        (contains? numeric-functions (first expr))
	  (make-numeric-form (check-hybrid-atom expr numeric-functions discrete-vars))
        :else 
	  (let [[op arity]   (safe-get {'* [* 2] '+ [+ 2] '- [- 2] 'abs [abs 1]} (first expr))]
	    (assert-is (= arity (count (next expr))) "%s" expr)
	    (make-numeric-expression op 
	      (map #(parse-and-check-numeric-expression % 
		     discrete-vars (when-not only-atomic-var?  numeric-vars) numeric-functions)
		   (next expr)))))))

	  
(deftest numeric-exprs 
  (is (= 25
	 (evaluate-numeric-expr 
	  (parse-and-check-numeric-expression '(+ (- c 2) [gt a b]) 
					      {'a 't1 'b 't2} {'c 'x} {'gt ['t1 't2]} )
	  {'c 12 'a 'aa 'b 'bb} {'[gt aa bb] 15} ))))

 
;; Constraints

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
   (evaluate-numeric-expr (:left constraint) var-map numeric-vals)
   (evaluate-numeric-expr (:right constraint) var-map numeric-vals)))

(defmethod split-constraint ::NumConstraint [constraint var-map objects]
  [nil nil constraint])

(defmethod get-numeric-yield ::NumConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (if (isa? (:class (:left constraint)) ::NumVar) 
      [(make-numeric-constraint (:pred constraint) (:left constraint) 
	 (make-numeric-constant (evaluate-numeric-expr (:right constraint) var-map numeric-vals)))]
    (when (evaluate-constraint constraint var-map objects [discrete-atoms numeric-vals]) [])))


(defmethod extract-difference-constraints ::NumConstraint 
  [constraint var-map constant-numeric-functions numeric-vals] 
  (let [{:keys [pred left right]} constraint
	left  (ground-and-simplify-numeric-expr left var-map constant-numeric-functions numeric-vals)
	right (ground-and-simplify-numeric-expr right var-map constant-numeric-functions numeric-vals)]
    (assert-is (contains? #{::NumVar ::NumForm} (:class left)))
    (apply make-hybrid-strips-difference-constraint 
	   pred 
	   left
	   (extract-numeric-expr-form-and-diff right))))					




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
	    (make-discrete-neg-constraint (check-hybrid-atom (second constraint) predicates discrete-vars))
          (contains? predicates f)
	    (make-discrete-pos-constraint (check-hybrid-atom constraint predicates discrete-vars))
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
		 (parse-and-check-numeric-expression (nth constraint 1)
		   discrete-vars numeric-vars numeric-functions true)
		 (parse-and-check-numeric-expression (nth constraint 2)
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
  

;; Effects

(defstruct hybrid-strips-assignment :class :form :expr)
(defn make-assignment [form expr]
  (struct hybrid-strips-assignment ::Assignment form expr))

(defn execute-assignment [assignment var-map numeric-vals old-numeric-vals]
  (assoc numeric-vals
    (props/simplify-atom var-map (:form assignment))
    (evaluate-numeric-expr (:expr assignment) var-map old-numeric-vals)))


(defstruct hybrid-strips-effect :class :adds :deletes :assignments)
(defn make-effect [adds deletes assignments]
  (struct hybrid-strips-effect ::Effect adds deletes assignments))

(defn execute-effect [effect var-map [discrete-atoms numeric-vals]]
  (let [simplifier (fn [atoms] (map #(props/simplify-atom var-map %) atoms))]
    [(reduce conj 
      (reduce disj discrete-atoms (simplifier (:deletes effect)))
      (simplifier (:adds effect)))
     (reduce (fn [nv ae] (execute-assignment ae var-map nv numeric-vals)) numeric-vals (:assignments effect))]))
 

(def *empty-effect* (make-effect nil nil nil))

(defn parse-and-check-effect [effect discrete-vars predicates numeric-vars numeric-functions]
  (let [effects (if (or (empty? effect) (= (first effect) 'and)) (next effect) (list effect))
	{:keys [adds deletes assignments]}
          (group-by (fn [[a]] (cond (= a '=) :assignments (= a 'not) :deletes :else :adds)) effects)]
;    (println adds deletes assignments)
    (make-effect 
     (doall (for [a adds] 
	      (check-hybrid-atom a predicates discrete-vars)))
     (doall (for [a deletes] 
	      (do (assert-is (= 2 (count a))) 
		  (check-hybrid-atom (second a) predicates discrete-vars))))
     (doall (for [a assignments] 
	      (do (assert-is (= 3 (count a))) 
		  (make-assignment (check-hybrid-atom (nth a 1) numeric-functions discrete-vars)
				   (parse-and-check-numeric-expression (nth a 2) discrete-vars numeric-vars numeric-functions))))))))
	 

(defn effected-predicates [effect]
  (set (map first (concat (:adds effect) (:deletes effect)))))

(defn effected-functions [effect]
  (set (map first (map :form (:assignments effect)))))

(deftest hybrid-effects
  (is
   (= ['#{[fee] [frob xv] [bar xv]} '{[fra] 17 [frax xv] 13 }]
      (execute-effect 
       (parse-and-check-effect '(and (fee) (frob x) (not (foo x)) (not (bar x)) (bar x) 
				     (= (fra) z) (= (frax x) (+ (frax x) (- (fra) 2)))) 
			       '{x xt} '{foo [xt] frob [xt] bar [xt] fee []} '{z zt} '{frax [xt] fra []})
       '{x xv z 17} ['#{[foo xv] [bar xv]} '{[frax xv] 1 [fra] 14}]))))

