(ns edu.berkeley.ai.envs.hybrid-strips.constraints
  (:use clojure.test   )
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [propositions :as props] [intervals :as iv]
	     [hybrid :as hybrid] [linear-expressions :as le]]
		[edu.berkeley.ai.envs :as envs]
	    ))

;; Here, we assume a hybrid state is a [discrete-atom-set numeric-val-map] pair.

;; Just ground the expr for now, for kicks. 
;(defmulti ground-hybrid-constraint (fn [constraint discrete-var-map constant-numeric-vals] (:class; constraint)))

(defmulti evaluate-constraint 
  "Evaluate if the constraint is true or false in the given state."
  (fn [constraint var-map objects [discrete-atoms numeric-vals]] (:class constraint))) 

(defmulti split-constraint 
  "Return [pos-atoms neg-atoms remaining-constraints], where we've pulled out as much of the 
   propositional content as possible, including expanding forall conditions with 
   empty conditions.  If no foralls have propositional yields, remaining-constraints
   will include only numeric (and numeric forall) constraints. "
  (fn [constraint var-map objects] (:class constraint)))

(defmulti get-numeric-yield 
  "Get nil (false) or a possibly-empty list of numeric constraints, 
   where the :left is a single ::NumVar expression."
  (fn [constraint var-map objects [discrete-atoms numeric-vals]] (:class constraint)))

(defmulti get-fn-yield 
  "Get a list of functions that can be applied to constrain the state."
  (fn [constraint disc-var-map cont-var-map const-fns lez-fn eqz-fn gez-fn] (:class constraint)))
  
(defmulti apply-constraint 
  "Apply the constraint, and return a seq of resulting states.
   pos/neg-fun applies a single discrete effect to the state, returning a new state or nil.
   lez-fn, eqz-fn, and gez-fn do the same thing for a numeric constraint."
  (fn [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn] (:class constraint)))

(defmulti apply-constraint-and-negation
  "Do our best to apply the constraint and its negation, and return a pair of seqs of resulting states [pos neg].
   Ignore inversions of strict equality. 
   pos/neg-fun applies a single discrete effect to the state, returning a new state or nil.
   lez-fn, eqz-fn, and gez-fn do the same thing for a numeric constraint."
  (fn [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn] (:class constraint)))



(derive ::NumConstraint ::Constraint)
(defstruct hybrid-strips-numeric-constraint :class :pred :left :right)
(defn make-numeric-constraint [pred left right]
  (struct hybrid-strips-numeric-constraint ::NumConstraint pred left right))

;(defmethod ground-hybrid-constraint ::NumConstraint [constraint disc-var-map const-num-vals]
;  (assoc constraint 
;    :left (le/ground-hybrid-linear-expr (:left constraint) disc-var-map const-num-vals)
;    :right (le/ground-hybrid-linear-expr (:right constraint) disc-var-map const-num-vals)))

(defmethod evaluate-constraint ::NumConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  ((:pred constraint)
   (le/evaluate-hybrid-linear-expr (:left constraint) var-map numeric-vals)
   (le/evaluate-hybrid-linear-expr (:right constraint) var-map numeric-vals)))

(defmethod split-constraint ::NumConstraint [constraint var-map objects]
  [nil nil constraint])

(defmethod get-numeric-yield ::NumConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (let [sv (le/extract-singleton-var (:left constraint))]
    (if (and sv (not (coll? sv)))
      [(make-numeric-constraint (:pred constraint) (:left constraint) 
	 {nil (le/evaluate-hybrid-linear-expr (:right constraint) var-map numeric-vals)})]
    (when (evaluate-constraint constraint var-map objects [discrete-atoms numeric-vals]) []))))

(defmethod get-fn-yield ::NumConstraint [constraint disc-var-map cont-var-map const-fns lez-fn eqz-fn gez-fn]
  (let [lm (merge-with + (le/hybrid-linear-expr->grounded-lm (:left constraint) disc-var-map 
                                                             cont-var-map const-fns)
                (util/map-vals - (le/hybrid-linear-expr->grounded-lm (:right constraint) disc-var-map 
                                                                     cont-var-map const-fns)))]
    [(condp = (:pred constraint)
        <  #(lez-fn % lm true)
        <= #(lez-fn % lm false)
        =  #(eqz-fn % lm)
        >= #(gez-fn % lm false)
        >  #(gez-fn % lm true))]))

;; TODO: figure out strict constraints.
(defmethod apply-constraint ::NumConstraint [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn]
  (when-let [new-state 
             ((util/safe-singleton (get-fn-yield constraint disc-var-map cont-var-map 
                                                 const-fns lez-fn eqz-fn gez-fn))
              state)]
    [new-state]))


(defmethod apply-constraint-and-negation ::NumConstraint 
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn]
  (let [pos (apply-constraint state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil)]
    (if (empty? pos) 
        [[] [state]]
      [pos 
       (if (= = (:pred constraint)) [state]
	 (apply-constraint state 
	   (update-in constraint [:pred] #(condp = % <= > >= < > <= < >=))
	   disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil))])))




(derive ::DiscPosConstraint ::Constraint)
(defstruct hybrid-strips-discrete-pos-constraint :class :atom)
(defn make-discrete-pos-constraint [atom]
  (struct hybrid-strips-discrete-pos-constraint ::DiscPosConstraint atom))

;(defmethod ground-hybrid-constraint ::DiscPosConstraint [constraint disc-var-map const-num-vals]
;  constraint)


(defmethod evaluate-constraint ::DiscPosConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint))))

(declare make-conjunctive-constraint)
(defmethod split-constraint ::DiscPosConstraint [constraint var-map objects]
  [[(props/simplify-atom var-map (:atom constraint))] nil (make-conjunctive-constraint nil)])

(defmethod apply-constraint ::DiscPosConstraint
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn]
  (when-let [new-state (pos-fn state (props/simplify-atom  disc-var-map (:atom constraint)))]
    [new-state]))

(defmethod apply-constraint-and-negation ::DiscPosConstraint 
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn]
 (let [pos (apply-constraint state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil)]
    (if (empty? pos) [[] [state]]
      [pos
       (apply-constraint state (assoc constraint :class ::DiscNegConstraint)
			 disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil)])))



(derive ::DiscNegConstraint ::Constraint)
(defstruct hybrid-strips-discrete-neg-constraint :class :atom)
(defn make-discrete-neg-constraint [atom]
  (struct hybrid-strips-discrete-neg-constraint ::DiscNegConstraint atom))

;(defmethod ground-hybrid-constraint ::DiscNegConstraint [constraint disc-var-map const-num-vals]
;  constraint)
 
(defmethod evaluate-constraint ::DiscNegConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (not (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint)))))

(defmethod split-constraint ::DiscNegConstraint [constraint var-map objects]
  [nil [(props/simplify-atom var-map (:atom constraint))] (make-conjunctive-constraint nil)])

(defmethod apply-constraint ::DiscNegConstraint
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn]
  (when-let [new-state (neg-fn state (props/simplify-atom disc-var-map (:atom constraint)))]
    [new-state]))

(defmethod apply-constraint-and-negation ::DiscNegConstraint 
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn]
 (let [pos (apply-constraint state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil)]
    (if (empty? pos) [[] [state]]
      [pos
       (apply-constraint state (assoc constraint :class ::DiscPosConstraint)
			 disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn nil)])))




(derive ::ConjunctiveConstraint ::Constraint)
(defstruct hybrid-strips-conjuntive-constraint :class :constraints)
(defn make-conjunctive-constraint [constraints]
  (struct hybrid-strips-conjuntive-constraint ::ConjunctiveConstraint constraints))

;(defmethod ground-hybrid-constraint ::ConjunctiveConstraint [constraint disc-var-map const-num-vals]
;  (assoc constraint :constraints
;    (map #(ground-hybrid-constraint % disc-var-map const-num-vals) (:constraints constraint))))

(defmethod evaluate-constraint ::ConjunctiveConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
;  (doseq [x (:constraints constraint)] (println x (evaluate-constraint x var-map objects [discrete-atoms numeric-vals])))
  (every? #(evaluate-constraint % var-map objects [discrete-atoms numeric-vals]) (:constraints constraint)))

(defmethod split-constraint ::ConjunctiveConstraint [constraint var-map objects]
  (let [bits (map #(split-constraint % var-map objects) (:constraints constraint))]
    [(apply concat (map first bits))
     (apply concat (map second bits))
     (make-conjunctive-constraint (apply concat (for [b bits 
                                                      :let [num (nth b 2)] :when num] 
                                                  (if (isa? (:class b) ::ConjunctiveConstraint)
                                                    (util/safe-get num :constraints)
                                                    [num]))))]))

(defmethod get-numeric-yield ::ConjunctiveConstraint  [constraint var-map objects [discrete-atoms numeric-vals]]
  (loop [constraints (seq (:constraints constraint)) yield []]
    (if constraints
        (when-let [c (get-numeric-yield (first constraints) var-map objects [discrete-atoms numeric-vals])]
	  (recur (next constraints) (into yield c)))
      yield)))

(defmethod get-fn-yield ::ConjunctiveConstraint [constraint disc-var-map cont-var-map const-fns lez-fn eqz-fn gez-fn]
  (mapcat #(get-fn-yield % disc-var-map cont-var-map const-fns lez-fn eqz-fn gez-fn)
          (util/safe-get constraint :constraints)))

(defmethod apply-constraint ::ConjunctiveConstraint
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn]
;  (println "Constraint"  constraint "\n\n")
  (let [constraints (util/group-by :class (util/safe-get constraint :constraints))]
    (util/reduce-while 
     (fn [states constraint] 
       (mapcat #(apply-constraint % constraint disc-var-map cont-var-map objects 
				  const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn)
	       states))
     [state]
     (apply concat (map constraints [::DiscNegConstraint ::DiscPosConstraint 
				     ::NumConstraint ::ForallConstraint])))))


;; Here we're guaranteed to have no "Forall" constraints. 
; Decompose things as TTTTT vs F, TF, TTF, TTTF, TTTF.
(defmethod apply-constraint-and-negation ::ConjunctiveConstraint 
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn]
  (loop [constraints (util/safe-get constraint :constraints) pos-state state neg-states []]
    (if (empty? constraints) [[pos-state] neg-states]
      (let [[constraint & more-constraints] constraints
	    [pos neg] (apply-constraint-and-negation pos-state constraint disc-var-map cont-var-map 
						     objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn)]
	(if (empty? pos)
	    [nil [state]]
	  (recur more-constraints
		 (util/safe-singleton pos)
		 (if (empty? neg) neg-states (conj neg-states (util/safe-singleton neg)))))))))
	  




(derive ::ForallConstraint ::Constraint)
(defstruct hybrid-strips-forall-constraint :class :vars :condition :yield)
(defn make-forall-constraint [vars condition yield]
  (struct hybrid-strips-forall-constraint ::ForallConstraint vars condition yield))

;(defmethod ground-hybrid-constraint ::ForallConstraint [constraint disc-var-map const-num-vals]
;  constraint)
;  (assoc constraint
;    :condition (ground-hybrid-constraint (:condition constraint) disc-var-map const-num-vals)
;    :yield     (ground-hybrid-constraint (:yield constraint) disc-var-map const-num-vals)))


(defmethod evaluate-constraint ::ForallConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (every? (fn [full-var-map] 
;	    (println full-var-map)
	    (or (not (evaluate-constraint (:condition constraint) full-var-map objects [discrete-atoms numeric-vals]))
		(evaluate-constraint (:yield constraint) full-var-map objects [discrete-atoms numeric-vals])))
	  (let [vars (seq (:vars constraint))]
	    (for [combo (apply util/cartesian-product (map #(get objects (first %)) vars))]
	      (into var-map (map (fn [val tv] [(second tv) val]) combo vars))))))

(defmethod split-constraint ::ForallConstraint [constraint var-map objects]
;  (println (:condition constraint) (isa? (:class constraint) ::ConjunctiveConstraint))
  (if (or (empty? (:condition constraint))
	  (and (isa? (:class (:condition constraint)) ::ConjunctiveConstraint)
	       (empty? (util/safe-get (:condition constraint) :constraints))))
      (let [var-maps
	     (let [vars (seq (:vars constraint))]
	       (for [combo (apply util/cartesian-product (map #(get objects (first %)) vars))]
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
	    (for [combo (apply util/cartesian-product (map #(get objects (first %)) vars))]
	      (into var-map (map (fn [val tv] [(second tv) val]) combo vars)))))]
    (loop [var-maps (seq consistent-var-maps) yield []]
      (if var-maps
        (when-let [c (get-numeric-yield (:yield constraint) (first var-maps) objects [discrete-atoms numeric-vals])]
	  (recur (next var-maps) (into yield c)))
	yield))))

(defmethod apply-constraint ::ForallConstraint
  [state constraint disc-var-map cont-var-map objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn]
  (let [vars (seq (:vars constraint))]
    (loop [var-maps (for [combo (apply util/cartesian-product (map #(get objects (first %)) vars))]
		      (into disc-var-map (map (fn [val tv] [(second tv) val]) combo vars)))
	   states [state]]
      (cond (empty? states) nil
	    (empty? var-maps) states 
	    :else 
	 (recur 
	  (rest var-maps)
	  (apply concat      
  	    (for [state states
                  :when (feasible?-fn state)]
	      (let [[pos neg] (apply-constraint-and-negation state (:condition constraint) (first var-maps) cont-var-map 
							     objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn)]
		(concat (mapcat #(apply-constraint % (:yield constraint) (first var-maps) cont-var-map 
						   objects const-fns pos-fn neg-fn lez-fn eqz-fn gez-fn feasible?-fn) 
				pos)
			neg)))))))))


(def *true-constraint* (make-conjunctive-constraint nil))


(declare parse-and-check-constraint)
(defn parse-and-check-nonconjunctive-constraint [constraint discrete-vars predicates numeric-vars numeric-functions const-numeric-functions only-atomic-var?]
  (let [[f & r] constraint]
    (cond (and (= f 'not) (contains? predicates (ffirst r)))
	    (make-discrete-neg-constraint (hybrid/check-hybrid-atom (second constraint) predicates discrete-vars))
          (contains? predicates f)
	    (make-discrete-pos-constraint (hybrid/check-hybrid-atom constraint predicates discrete-vars))
	  (= f 'forall)
	    (do (let [vars (props/parse-typed-pddl-list (nth constraint 1))
		      all-discrete (into discrete-vars (map (fn [[t v]] [v t]) vars))]
		  (util/assert-is (= (count all-discrete) (+ (count vars) (count discrete-vars))))
		  (make-forall-constraint
		   vars
		   (parse-and-check-constraint (nth constraint 2) all-discrete predicates 
					       (when-not only-atomic-var? numeric-vars)
					       numeric-functions const-numeric-functions 
					       only-atomic-var?)
		   (parse-and-check-constraint (nth constraint 3) all-discrete predicates 
					       numeric-vars 
					       numeric-functions const-numeric-functions
					       only-atomic-var?))))
	  :else
	    (do (util/assert-is (= (count constraint) 3) "%s" constraint)
		(make-numeric-constraint 
		 (util/safe-get {'= = '< < '> > '<= <= '>= >=} f)
		 (le/parse-and-check-hybrid-linear-expression (nth constraint 1)
		   discrete-vars numeric-vars numeric-functions const-numeric-functions #_true)
		 (le/parse-and-check-hybrid-linear-expression (nth constraint 2)
		   discrete-vars  (when-not only-atomic-var? numeric-vars)
		   numeric-functions const-numeric-functions))))))
		      
(defn parse-and-check-constraint 
  ([constraint discrete-vars predicates numeric-vars numeric-functions const-numeric-functions]
     (parse-and-check-constraint constraint discrete-vars predicates numeric-vars numeric-functions const-numeric-functions false))
  ([constraint discrete-vars predicates numeric-vars numeric-functions const-numeric-functions only-atomic-var?]
;  (println constraint)
  (if (or (empty? constraint) (= (first constraint) 'and))
      (make-conjunctive-constraint 
       (doall
	(for [sub (next constraint)] 
	 (parse-and-check-nonconjunctive-constraint sub discrete-vars predicates numeric-vars numeric-functions const-numeric-functions only-atomic-var?))))
    (parse-and-check-nonconjunctive-constraint constraint discrete-vars predicates numeric-vars numeric-functions const-numeric-functions only-atomic-var?))))

; Constraints as envs.conditions.

(derive ::ConstraintCondition ::envs/Condition)
(defstruct constraint-condition :class :constraint :objects :var-map :known-consistent?)

(defn make-constraint-condition [constraint objects var-map known-consistent?] 
  (struct constraint-condition ::ConstraintCondition constraint objects var-map known-consistent?))

(defmethod envs/satisfies-condition? ::ConstraintCondition [s c]
  (evaluate-constraint (:constraint c) (:var-map c) (:objects c) s))

(defmethod envs/consistent-condition? ::ConstraintCondition [condition]
  (or (:known-consistent? condition) 
      (throw (UnsupportedOperationException.))))



(deftest constraints
  (is (evaluate-constraint (parse-and-check-constraint '(= 1 1) nil nil nil nil nil) nil nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(= 1 2) nil nil nil nil nil) nil nil [nil nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil nil) {'x 1 'y 1} nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil nil) {'x 2 'y 1} nil [nil nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(not (abc x y)) '{x xt y yt} '{abc [xt yt]} nil nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil])))
  (is (not (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil nil) 
				     '{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y2]} nil])))
  (is (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 2)) nil nil nil nil nil) nil nil [nil nil]))
  (is (not (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 1)) nil nil nil nil nil) nil nil [nil nil])))
  (is (not (evaluate-constraint (parse-and-check-constraint '(and (= 2 1) (= 1 1)) nil nil nil nil nil) nil nil [nil nil])))
  (is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x2] [bar x1] [bar x2]} nil]))
  (is (not (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x3] [bar x1] [bar x2]} nil])))
  (is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
	     '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]} nil) 
	    '{y yv z 17} '{xt [x1 x2 x3 x4] yt [yv]} 
	    ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
	    '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
	      [froxy x1 yv] 17, [froxy x2 yv] 17, [froxy x3 yv] 19, [froxy x4 yv] 17}]))
  (is (not (evaluate-constraint 
;	      (ground-hybrid-constraint 
		 (parse-and-check-constraint 
		  '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
		  '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]} nil)
;		 '{y yv} {})
	      '{z 17 y yv} '{xt [x1 x2 x3 x4] yt [yv]} 
	      ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
	       '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
		 [froxy x1 yv] 17, [froxy x2 yv] 16, [froxy x3 yv] 19, [froxy x4 yv] 17}]))))
  




(comment ;old, not in use

; Idea: left - right = diff, diff is a number, left may be a var or form, right must be a form or constant .
; This is the restricted form of numeric constraint allowed in hybrid-strips for now.
(defstruct hybrid-strips-difference-constraint :pred :left :right :diff)
(defn make-hybrid-strips-difference-constraint [pred left right diff]
  (struct hybrid-strips-difference-constraint pred left right diff))

(defmulti extract-difference-constraints (fn [constraint var-map constant-numeric-functions numeric-vals] (:class constraint)))

;; Extract a set of difference constraints

;; TODO: abstraction violations.
(defmethod extract-difference-constraints ::NumConstraint 
  [constraint var-map constant-numeric-functions numeric-vals] 
  (let [{:keys [pred left right]} constraint
	left  (le/ground-and-simplify-hybrid-linear-expr left var-map constant-numeric-functions numeric-vals)
	right (le/ground-and-simplify-hybrid-linear-expr right var-map constant-numeric-functions numeric-vals)]
    (util/assert-is (contains? #{::le/NumVar ::le/NumForm} (:class left)))
    (apply make-hybrid-strips-difference-constraint 
	   pred 
	   left
	   (le/extract-hybrid-linear-expr-form-and-diff right))))

(defmethod extract-difference-constraints ::ConjunctiveConstraint [constraint var-map constant-numeric-functions numeric-vals] 
  (apply concat (map #(extract-difference-constraints % var-map constant-numeric-functions numeric-vals) (:constraints constraint))))
)