(ns edu.berkeley.ai.domains.hybrid-strips
 (:require [edu.berkeley.ai.util.propositions :as props]
           [edu.berkeley.ai [util :as util] [envs :as envs]]
           [edu.berkeley.ai.envs.states.binary :as binary-states])
;           [edu.berkeley.ai.domains.hybrid_strips domains])
 )



;;; Hybrid STRIPS domains
; In addition to usual features, have set of (real) numeric types and 
; set of numeric functions (otherwise like predicates).
; Numbers can be compared with the special predicates "=", "<", "<=", ">", ">=",
  ; negation not allowed.
; Linear functions of numbers are allowed.
; Effect literals for numbers take form (= (num-fn ...) new-value).
; Preconditions may include (forall (binding-params) (when) (precond)) forms.

; Right now, specific syntactic restrictions on constraints:
 ; Numeric vars can only appear in the left side of a comparison, not in expressions
   ; (except cost), and not in conditions of foralls
 ; The set of applicable discrete conditions must be computable statically,
   ; i.e., when in a forall, must have no condition.

;; STRIPS action schemata


;;; States are [discrete-atoms numeric-vals]


;;; Helper types for expressions, assignments, and conditions

;; Helper

(defn- check-atom [atom arg-map var-types]
;  (println atom arg-map var-types)
  (let [args (util/safe-get arg-map (first atom))
	body (next atom)]
    (util/assert-is (= (count body) (count args)))
    (doseq [[v t] (map vector body args)]
      (util/assert-is (= t (get var-types v)) "%s %s %s" atom args var-types))
    (vec atom)))

;; Expressions

(defmulti evaluate-numeric-expr (fn [expr var-map numeric-vals] (:class expr))) 


(derive ::NumConst ::Num)
(defstruct hybrid-strips-numeric-constant :class :constant)
(defn- make-numeric-constant [constant]
;  (util/assert-is (number? constant))
  (struct hybrid-strips-numeric-constant ::NumConst constant))

(defmethod evaluate-numeric-expr ::NumConst [expr var-map numeric-vals]
  (:constant expr))


(derive ::NumVar ::Num)
(defstruct hybrid-strips-numeric-var :class :var)
(defn- make-numeric-var [var]
  (struct hybrid-strips-numeric-var ::NumVar var))

(defmethod evaluate-numeric-expr ::NumVar [expr var-map numeric-vals]
  (util/safe-get var-map (:var expr)))


(derive ::NumForm ::Num)
(defstruct hybrid-strips-numeric-form :class :form)
(defn- make-numeric-form [form]
  (struct hybrid-strips-numeric-form ::NumForm form))

(defmethod evaluate-numeric-expr ::NumForm [expr var-map numeric-vals]
  ;(println var-map)
  (util/safe-get numeric-vals (props/simplify-atom var-map (:form expr))))


(derive ::NumExpr ::Num)
(defstruct hybrid-strips-numeric-expression :class :op :left :right)
(defn- make-numeric-expression [op left right]
  (struct hybrid-strips-numeric-expression ::NumExpr op left right))

(defmethod evaluate-numeric-expr ::NumExpr [expr var-map numeric-vals]
  ((:op expr)
   (evaluate-numeric-expr (:left expr) var-map numeric-vals)
   (evaluate-numeric-expr (:right expr) var-map numeric-vals)))


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
	  (make-numeric-form (check-atom expr numeric-functions discrete-vars))
        :else 
          (do (util/assert-is (= (count expr) 3))
	      (let [op   (util/safe-get {'* * '+ + '- -} (first expr))
		    left (parse-and-check-numeric-expression (nth expr 1)
			  discrete-vars (when-not only-atomic-var?  numeric-vars) numeric-functions )
		    right (parse-and-check-numeric-expression  (nth expr 2)
			  discrete-vars (when-not only-atomic-var? numeric-vars) numeric-functions)]
;		  (when (= op *) 
;		    (util/assert-is (or (isa? (:class left) ::NumConst) 
;					(isa? (:class right) ::NumConst))))
		  (make-numeric-expression op left right))))))
	  
(util/deftest numeric-exprs 
  (util/is (= 25
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


(derive ::NumConstraint ::Constraint)
(defstruct hybrid-strips-numeric-constraint :class :pred :left :right)
(defn- make-numeric-constraint [pred left right]
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



(derive ::DiscPosConstraint ::Constraint)
(defstruct hybrid-strips-discrete-pos-constraint :class :atom)
(defn- make-discrete-pos-constraint [atom]
  (struct hybrid-strips-discrete-pos-constraint ::DiscPosConstraint atom))

(defmethod evaluate-constraint ::DiscPosConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint))))

(defmethod split-constraint ::DiscPosConstraint [constraint var-map objects]
  [[(props/simplify-atom var-map (:atom constraint))] nil nil])


(derive ::DiscNegConstraint ::Constraint)
(defstruct hybrid-strips-discrete-neg-constraint :class :atom)
(defn- make-discrete-neg-constraint [atom]
  (struct hybrid-strips-discrete-neg-constraint ::DiscNegConstraint atom))

(defmethod evaluate-constraint ::DiscNegConstraint [constraint var-map objects [discrete-atoms numeric-vals]]
  (not (contains? discrete-atoms (props/simplify-atom var-map (:atom constraint)))))

(defmethod split-constraint ::DiscNegConstraint [constraint var-map objects]
  [nil [(props/simplify-atom var-map (:atom constraint))] nil])



(derive ::ConjunctiveConstraint ::Constraint)
(defstruct hybrid-strips-conjuntive-constraint :class :constraints)
(defn- make-conjunctive-constraint [constraints]
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


(derive ::ForallConstraint ::Constraint)
(defstruct hybrid-strips-forall-constraint :class :vars :condition :yield)
(defn- make-forall-constraint [vars condition yield]
  (struct hybrid-strips-forall-constraint ::ForallConstraint vars condition yield))

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





(declare parse-and-check-constraint)
(defn parse-and-check-nonconjunctive-constraint [constraint discrete-vars predicates numeric-vars numeric-functions only-atomic-var?]
  (let [[f & r] constraint]
    (cond (and (= f 'not) (contains? predicates (ffirst r)))
	    (make-discrete-neg-constraint (check-atom (second constraint) predicates discrete-vars))
          (contains? predicates f)
	    (make-discrete-pos-constraint (check-atom constraint predicates discrete-vars))
	  (= f 'forall)
	    (do (let [vars (props/parse-typed-pddl-list (nth constraint 1))
		      all-discrete (into discrete-vars (map (fn [[t v]] [v t]) vars))]
		  (util/assert-is (= (count all-discrete) (+ (count vars) (count discrete-vars))))
		  (make-forall-constraint
		   vars
		   (parse-and-check-constraint (nth constraint 2) all-discrete predicates 
					       (when-not only-atomic-var? numeric-vars)
					       numeric-functions only-atomic-var?)
		   (parse-and-check-constraint (nth constraint 3) all-discrete predicates 
					       numeric-vars 
					       numeric-functions only-atomic-var?))))
	  :else
	    (do (util/assert-is (= (count constraint) 3) "%s" constraint)
		(make-numeric-constraint 
		 (util/safe-get {'= = '< < '> > '<= <= '>= >=} f)
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


(util/deftest constraints
  (util/is (evaluate-constraint (parse-and-check-constraint '(= 1 1) nil nil nil nil) nil nil [nil nil]))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(= 1 2) nil nil nil nil) nil nil [nil nil])))
  (util/is (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil) {'x 1 'y 1} nil [nil nil]))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(= x y) nil nil {'x 't 'y 't} nil) {'x 2 'y 1} nil [nil nil])))
  (util/is (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil]))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(not (abc x y)) '{x xt y yt} '{abc [xt yt]} nil nil) 
				'{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y1]} nil])))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(abc x y) '{x xt y yt} '{abc [xt yt]} nil nil) 
				     '{x x1 y y1} '{xt [x1] yt [y1]} ['#{[abc x1 y2]} nil])))
  (util/is (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 2)) nil nil nil nil) nil nil [nil nil]))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(and (= 1 1) (= 2 1)) nil nil nil nil) nil nil [nil nil])))
  (util/is (not (evaluate-constraint (parse-and-check-constraint '(and (= 2 1) (= 1 1)) nil nil nil nil) nil nil [nil nil])))
  (util/is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x2] [bar x1] [bar x2]} nil]))
  (util/is (not (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (foo x) (bar x)) 
	     '{} '{foo [xt] bar [xt]} nil nil) 
	    {} '{xt [x1 x2 x3]} ['#{[foo x1] [foo x3] [bar x1] [bar x2]} nil])))
  (util/is (evaluate-constraint 
	    (parse-and-check-constraint 
	     '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
	     '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]}) 
	    '{y yv z 17} '{xt [x1 x2 x3 x4] yt [yv]} 
	    ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
	    '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
	      [froxy x1 yv] 17, [froxy x2 yv] 17, [froxy x3 yv] 19, [froxy x4 yv] 17}]))
  (util/is (not (evaluate-constraint 
		 (parse-and-check-constraint 
		  '(forall (x - xt) (and (foo x y) (< (frox x) (froy y))) (and (bar x) (= (froxy x y) z))) 
		  '{y yt} '{foo [xt yt] bar [xt]} '{z zt} '{frox [xt] froy [yt] froxy [xt yt]}) 
		 '{y yv z 17} '{xt [x1 x2 x3 x4] yt [yv]} 
		 ['#{[foo x1 yv] [foo x2 yv] [foo x3 yv] [bar x1] [bar x2]}
		 '{[frox x1] 1, [frox x2] 2, [frox x3] 3, [frox x4] 1, [froy yv] 3,
		   [froxy x1 yv] 17, [froxy x2 yv] 16, [froxy x3 yv] 19, [froxy x4 yv] 17}]))))
  

;; Effects

(defstruct hybrid-strips-assignment :class :form :expr)
(defn- make-assignment [form expr]
  (struct hybrid-strips-assignment ::Assignment form expr))

(defn- execute-assignment [assignment var-map numeric-vals old-numeric-vals]
  (assoc numeric-vals
    (props/simplify-atom var-map (:form assignment))
    (evaluate-numeric-expr (:expr assignment) var-map old-numeric-vals)))


(defstruct hybrid-strips-effect :class :adds :deletes :assignments)
(defn- make-effect [adds deletes assignments]
  (struct hybrid-strips-effect ::Effect adds deletes assignments))

(defn- execute-effect [effect var-map [discrete-atoms numeric-vals]]
  (let [simplifier (fn [atoms] (map #(props/simplify-atom var-map %) atoms))]
    [(reduce conj 
      (reduce disj discrete-atoms (simplifier (:deletes effect)))
      (simplifier (:adds effect)))
     (reduce (fn [nv ae] (execute-assignment ae var-map nv numeric-vals)) numeric-vals (:assignments effect))]))
 


(defn parse-and-check-effect [effect discrete-vars predicates numeric-vars numeric-functions]
  (let [effects (if (= (first effect) 'and) (next effect) (list effect))
	{:keys [adds deletes assignments]}
          (util/group-by (fn [[a]] (cond (= a '=) :assignments (= a 'not) :deletes :else :adds)) effects)]
    (make-effect 
     (doall (for [a adds] 
	      (check-atom a predicates discrete-vars)))
     (doall (for [a deletes] 
	      (do (util/assert-is (= 2 (count a))) 
		  (check-atom (second a) predicates discrete-vars))))
     (doall (for [a assignments] 
	      (do (util/assert-is (= 3 (count a))) 
		  (make-assignment (check-atom (nth a 1) numeric-functions discrete-vars)
				   (parse-and-check-numeric-expression (nth a 2) discrete-vars numeric-vars numeric-functions))))))))
	 
(util/deftest hybrid-effects
  (util/is
   (= ['#{[fee] [frob xv] [bar xv]} '{[fra] 17 [frax xv] 13 }]
      (execute-effect 
       (parse-and-check-effect '(and (fee) (frob x) (not (foo x)) (not (bar x)) (bar x) 
				     (= (fra) z) (= (frax x) (+ (frax x) (- (fra) 2)))) 
			       '{x xt} '{foo [xt] frob [xt] bar [xt] fee []} '{z zt} '{frax [xt] fra []})
       '{x xv z 17} ['#{[foo xv] [bar xv]} '{[frax xv] 1 [fra] 14}]))))


;; Action Schemata


(defstruct hybrid-strips-action-schema 
  :class :name :vars :split-points :precondition :effect :cost-expr)

(defn make-hybrid-action-schema [name vars split-points precondition effect cost-expr]
  (struct hybrid-strips-action-schema ::HybridActionSchema 
    name vars split-points precondition effect cost-expr))

(defn- parse-hybrid-action-schema [action discrete-types numeric-types predicates numeric-functions]
;  (println action discrete-types numeric-types predicates numeric-functions)
  (util/match [[[:action       ~name]
		[:parameters   ~parameters]
		[:optional [:split-points ~split-points]]
		[:precondition ~precondition]
		[:effect       ~effect]
		[:optional [:cost  ~cost]]]
	       (util/partition-all 2 action)]
    (let [vars (props/parse-typed-pddl-list parameters)
	  [discrete-vars numeric-vars] 
	    (map (fn [vars] (into {} (map (fn [[t v]] [v t]) vars)))
	     (util/separate 
	      (fn [[t v]] 
		(cond (contains? discrete-types t) true
		      (contains? numeric-types t)  false
		      :else (throw (IllegalArgumentException.))))
	      vars))]
 ;     (println vars discrete-vars numeric-vars)
      (util/assert-is (<= (count numeric-vars) 1))
      (make-hybrid-action-schema
       name
       vars 
       (parse-and-check-constraint split-points discrete-vars predicates numeric-vars numeric-functions true)
       (parse-and-check-constraint precondition discrete-vars predicates numeric-vars numeric-functions true)
       (parse-and-check-effect     effect       discrete-vars predicates numeric-vars numeric-functions)
       (parse-and-check-numeric-expression (or cost 1) discrete-vars numeric-vars numeric-functions)))))



	    
;;; Hybrid-strips domains

; discrete-types and numeric-types are sets of types (no inheritance for now)
; predicates is a map from predicate names to seqs of argument types
; numeric-functions is a map from function names to seqs of argument types (return type being dropped for now).
; action-schemata is a map from schema names to schema objects

(derive ::HybridStripsPlanningDomain ::envs/PropositionalDomain)

(defstruct hybrid-strips-planning-domain 
  :class :name :discrete-types :numeric-types :predicates :numeric-functions :action-schemata :equality?)

(defn- make-hybrid-strips-planning-domain 
  [name discrete-types numeric-types predicates numeric-functions action-schemata equality?]
  (struct hybrid-strips-planning-domain ::HybridStripsPlanningDomain
	  name discrete-types numeric-types predicates numeric-functions action-schemata equality?))

(defn- check-numeric-functions [numeric-functions discrete-type-map numeric-types]
  (let [tl (props/parse-typed-pddl-list numeric-functions)]
    (doseq [[t f] tl] (util/assert-is (contains? numeric-types t)))
    (props/check-predicates discrete-type-map (map #(props/parse-pddl-predicate (second %)) tl))))

(defn read-hybrid-strips-planning-domain [file]
  (util/match [[define [domain ~name]
		[:requirements ~@requirements]
		[:types ~@discrete-types]
		[:numeric-types ~@numeric-types]
		[:predicates ~@predicates]
		[:numeric-functions ~@numeric-functions]
		~@actions]
	       (read-string (.toLowerCase (slurp file)))]
    (util/assert-is (apply distinct? discrete-types))
    (util/assert-is (apply distinct? numeric-types))
    (let [requirements   (set requirements)
	  discrete-types (set discrete-types)
	  numeric-types  (set numeric-types)
	  equality?      (contains? requirements :equality)
	  discrete-type-map (into {} (map vector discrete-types (repeat nil)))
	  predicates     (props/check-predicates discrete-type-map
			   (concat (map props/parse-pddl-predicate predicates)
			     (when equality? (map #(vector (util/symbol-cat % '=) % %) discrete-types))))
	  numeric-functions (check-numeric-functions numeric-functions discrete-type-map numeric-types)
	  action-schemata   (map #(parse-hybrid-action-schema % discrete-types numeric-types predicates numeric-functions)
				 actions)]
      (util/assert-is (util/subset? requirements #{:strips :typing :equality :numbers}))
      (util/assert-is (util/subset? #{:strips :typing :numbers} requirements))
      (util/assert-is (empty? (util/intersection discrete-types numeric-types)))
      (doseq [p (concat (keys predicates) (keys numeric-functions))] 
	(util/assert-is (not (contains? '#{= < <= > >= * + -} p))))
      (util/assert-is (apply distinct? (concat (keys predicates) (keys numeric-functions))))
      (util/assert-is (apply distinct? (map :name action-schemata)))
      (make-hybrid-strips-planning-domain 
       name
       discrete-types
       numeric-types
       predicates
       numeric-functions
       (into {} (map #(vector (util/safe-get % :name) %) action-schemata))
       equality?))))
 


 
;  (read-hybrid-strips-planning-domain "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.pddl")


;;; State space.

(derive ::HybridStateSpace ::edu.berkeley.ai.envs.states/StateSpace)

(defstruct hybrid-state-space :class :fluent-atoms :numeric-atoms :str-fn) 

(defn make-hybrid-state-space [fluent-atoms numeric-atoms str-fn]
  (struct hybrid-state-space ::HybridStateSpace (util/to-set fluent-atoms) (util/to-set numeric-atoms) str-fn))

(defmethod edu.berkeley.ai.envs.states/list-states ::HybridStateSpace [state-set]
  (throw (UnsupportedOperationException.)))

(defmethod edu.berkeley.ai.envs.states/canonicalize ::HybridStateSpace [state-set]
  state-set)  

(defmethod edu.berkeley.ai.envs.states/set-contains? ::HybridStateSpace [state-set elt]
  (and (every? (:fluent-atoms state-set) (first elt))
       (= (set (keys (second elt))) (:numeric-atoms state-set))))



;; Actions and action space

; Constraints

(derive ::ConstraintCondition ::envs/Condition)
(defstruct constraint-condition :class :constraint :objects :var-map)

(defn make-constraint-condition [constraint objects var-map] 
  (struct constraint-condition ::ConstraintCondition constraint objects var-map))

(defmethod envs/satisfies-condition? ::ConstraintCondition [s c]
 ; (println (:constraint c) (:var-map c) (:objects c))
  (evaluate-constraint (:constraint c) (:var-map c) (:objects c) s))

(defmethod envs/consistent-condition? ::ConstraintCondition [condition]
  (throw (UnsupportedOperationException.)))


; Instantiated actions

;(defstruct hybrid-strips-action :schema :var-map)

(defn- hybrid-strips-action->action [schema var-map action-space]
;  (println var-map)
  (let [effect (util/safe-get schema :effect)
	cost-expr (util/safe-get schema :cost-expr)]
    (envs/make-action 
     (vec (cons (:name schema) (map #(util/safe-get var-map (second %)) (:vars schema))))
     (fn [state] 
       [(execute-effect effect var-map state)
	(- (evaluate-numeric-expr cost-expr var-map (second state)))])
     (make-constraint-condition (util/safe-get schema :precondition) (util/safe-get action-space :objects) var-map))))

(defn get-hs-action 
  ([instance full-name]
     (let [schema (util/safe-get-in instance [:domain :action-schemata (first full-name)])]
       (hybrid-strips-action->action schema (into {} (map #(vector (second %1) %2) (util/safe-get schema :vars) (rest full-name))) (:action-space instance))))
  ([instance name var-map]
     (hybrid-strips-action->action (util/safe-get-in instance [:domain :action-schemata name]) var-map (:action-space instance))))

; Quasi-instantiated actions


; Action space (TODO)


(import '(java.util HashMap HashSet Arrays ArrayList))
(set! *warn-on-reflection* true)

(defn- get-next-atom [actions blacklist]
  (let [#^HashMap atom-counts (HashMap.)]
    (doseq [action actions]
      (doseq [p (:pos action)] (.put atom-counts p (inc (or (.get atom-counts p) 0))))
      (doseq [n (:neg action)] (.put atom-counts n (inc (or (.get atom-counts n) 0)))))
    (doseq [atom blacklist] (.remove atom-counts atom))
    (when-not (.isEmpty atom-counts)
      (key (util/first-maximal-element val atom-counts)))))


(defn- make-successor-generator 
  ([actions] (make-successor-generator actions nil))
  ([actions blacklist]
  (util/timeout)
  (let [most-common-atom (get-next-atom actions blacklist)]
    (if (nil? most-common-atom) 
        (fn [state] actions)
      (let [pos-list (ArrayList.)
	    neg-list (ArrayList.)
	    dc-list  (ArrayList.)]
	(doseq [action actions]
	  (let [in-pos? (contains? (:pos action) most-common-atom)
		in-neg? (contains? (:neg action) most-common-atom)]
	    (cond (and in-pos? in-neg?) nil ;(prn "Warning: contradictory preconditions for action" action) 
		  (and in-pos? (not in-neg?)) (.add pos-list action)
		  (and in-neg? (not in-pos?)) (.add neg-list action)
		  :else                       (.add dc-list action))))
	(let [pos-actions (seq pos-list)
	      neg-actions (seq neg-list)
	      dc-actions  (seq dc-list)
	    next-blacklist (cons most-common-atom blacklist)
	    pos-branch (if pos-actions (make-successor-generator pos-actions next-blacklist) (constantly nil))
	    neg-branch (if neg-actions (make-successor-generator neg-actions next-blacklist) (constantly nil))
	    dc-branch  (if dc-actions  (make-successor-generator dc-actions  next-blacklist) (constantly nil))]
	(fn [state] (concat (if (contains? state most-common-atom) (pos-branch state) (neg-branch state)) (dc-branch state))))))))) 

(set! *warn-on-reflection* false)

       
(defstruct hybrid-action-space :class :discrete-generator :objects :discrete-grid-size)

(defstruct hybrid-strips-quasi-action :schema :var-map :pos :neg :num-vars :num)

(defn- make-hybrid-action-space [discrete-types objects action-schemata discrete-grid-size]
;  (println (first action-schemata));(map :effect action-schemata))
  (struct hybrid-action-space ::HybridActionSpace
	(make-successor-generator 
  	  (for [schema (vals action-schemata)
	        :let [{:keys [vars precondition]} schema
		      [d-vars n-vars] (split-with #(contains? discrete-types (first %)) vars)]
		args (apply util/cartesian-product (map #(util/safe-get objects (first %)) d-vars))]
	  (let [var-map (into {} (map vector (map second d-vars) args))
		[p n num] (split-constraint precondition var-map objects)]
	    ;(println (:name schema) var-map p n)
	    (struct hybrid-strips-quasi-action schema var-map (set p) (set n) (set (map second n-vars)) num))))
	objects
	discrete-grid-size))
    


(defstruct interval :left :left-open :right :right-open)

(defn random-draw [interval]
  (let [l (:left interval) r (:right interval)]
    (util/assert-is (<= l r))
    (+ l (* (rand) (- r l)))))

(defn intersect-intervals [i1 i2]
  (let [l1 (:left i1) r1 (:right i1) lo1 (:left-open i1) ro1 (:right-open i1)
	l2 (:left i2) r2 (:right i2) lo2 (:left-open i2) ro2 (:right-open i2)]
    (struct interval 
	    (max l1 l2)
	    (cond (> l1 l2) lo1 (< l1 l2) lo2 :else (or lo1 lo2))
	    (min r1 r2)
	    (cond (< r1 r2) ro1 (> r1 r2) ro2 :else (or ro1 ro2)))))

(defn interval-contains? [i x]
  (and (or (> x (:left i))  (and (= x (:left i))  (not (:left-open i))))
       (or (< x (:right i)) (and (= x (:right i)) (not (:right-open i))))))

(def *real-line* (struct interval Double/NEGATIVE_INFINITY true Double/POSITIVE_INFINITY true))

(defmulti applicable-quasi-actions (fn [state action-space] (:class action-space)))

; TODO: prune empty intervals.
(defmethod applicable-quasi-actions ::HybridActionSpace [[discrete-atoms numeric-vals] action-space]
  (for [action ((:discrete-generator action-space) discrete-atoms)
	:let [{:keys [var-map num]} action ;(do (println (:name (:schema action)) (:var-map action)) action)
	      num (get-numeric-yield num var-map (:objects action-space) [discrete-atoms numeric-vals])]
	:when num]
    (let [num-vars    (:num-vars action)]
;      (println "done")
      (util/assert-is (<= (count num-vars) 1))
      (if (empty? num-vars)
          (do (util/assert-is (empty? num))
	      (assoc action :num {}))
	(assoc action :num
 	  {(first num-vars) 
	   (reduce intersect-intervals
		   *real-line*
		   (for [c num]
		     (let [{:keys [pred left right]} c
			   rval (:constant right)] 
			   ;(evaluate-numeric-expr right var-map numeric-vals)]
		       (util/assert-is (isa? (:class c) ::NumConstraint))
		       (util/assert-is (isa? (:class left) ::NumVar))
		       (util/assert-is (isa? (:class right) ::NumConst))
		       (util/assert-is (= (first num-vars) (:var left)))
		       (condp = pred
			 =  (struct interval rval false rval false)
			 <  (struct interval Double/NEGATIVE_INFINITY true rval true)
			 <= (struct interval Double/NEGATIVE_INFINITY true rval false)
			 >  (struct interval rval true Double/POSITIVE_INFINITY true)
			 >= (struct interval rval false Double/POSITIVE_INFINITY true)))))})))))


(defn quasi-action-numeric-intervals [action] ; Returns map from num-vars to intervals.
  (:num action))
		 
(defn ground-quasi-action 
  ([action num-var-map action-space]
     (util/assert-is (every? num-var-map (:num-vars action)))
     (hybrid-strips-action->action (:schema action) (merge num-var-map (:var-map action)) 
				   action-space)))

(defn discrete-quasi-action-instantiations [action action-space grid]
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (let [[var interval]  (first (:num action))]
 ;     (println (:name (:schema action)) (:var-map action) var interval)
      (for [i (range (int (Math/ceil (/ (:left interval) grid)))
		     (inc (int (Math/floor (/ (:right interval) grid)))))]		     
	(ground-quasi-action action {var (* i grid)} action-space)))))

(defn split-quasi-action-instantiations [[discrete-atoms numeric-vals] action action-space]
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (let [[var interval]   (first (:num action))
	  split-constraint (util/safe-get-in action [:schema :split-points])
	  split-clauses    (get-numeric-yield split-constraint 
			     (:var-map action) 
			     (:objects action-space) 
			     [discrete-atoms numeric-vals])
	  split-points     (distinct 
			    (for [c split-clauses]
			      (let [{:keys [class pred left right]} c]
				(util/assert-is (= class ::NumConstraint))
				(util/assert-is (= pred =))
				(util/assert-is (= (:class left) ::NumVar))
				(util/assert-is (= (:var left) var))
				(util/assert-is (= (:class right) ::NumConst))
				(util/safe-get right :constant))))]
;      (println interval split-points)
      (for [x split-points 
	    :when (interval-contains? interval x)]
	(ground-quasi-action action {var x} action-space)))))

      
;      (for [i (range (int (Math/ceil (/ (:left interval) grid)))
;		     (inc (int (Math/floor (/ (:right interval) grid)))))]		     
;	(ground-quasi-action action {var (* i grid)} action-space)))))


(defn all-quasi-action-instantiations [action action-space]
 ; (println (:name (:schema action)) (:var-map action))
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (repeatedly #(ground-quasi-action action
				      (util/map-vals random-draw (:num action))
				      action-space))))

(defn applicable-discrete-actions [[discrete-atoms numeric-vals] action-space grid]
 ; (println "discrete")
  (mapcat #(discrete-quasi-action-instantiations % action-space grid)
	  (applicable-quasi-actions [discrete-atoms numeric-vals] action-space)))

(defn applicable-split-actions [[discrete-atoms numeric-vals] action-space]
 ; (println "split")
  (mapcat #(split-quasi-action-instantiations [discrete-atoms numeric-vals] % action-space)
	  (applicable-quasi-actions [discrete-atoms numeric-vals] action-space)))

(defmethod envs/applicable-actions ::HybridActionSpace [state action-space]
  (if (:discrete-grid-size action-space) 
      (applicable-discrete-actions state action-space (:discrete-grid-size action-space))
    (applicable-split-actions state action-space)))

(defmethod envs/all-actions ::HybridActionSpace [action-space]
  (throw (UnsupportedOperationException.)))


; Tricky - for now, punt and require single numeric variable, not appearing in forall conditions.
; Build a little successor generator for finding consistent instantiations of discrete vars?
; Ignore yield of forall, just look at discrete 

; First stage: ground out discrete vars, run through successor generator 
 
; Second stage: for each action, collect conjunction of numeric constraints
; Separate into constraints involving numeric vars and others
; Filter on evaluation of others, and return set of quasi-ground actions

; Third stage: Instantiate ground action with numeric value

;;; Instances

(derive ::HybridStripsPlanningInstance ::envs/PropositionalEnvironment)
(defstruct hybrid-strips-planning-instance 
  :class :name :domain :objects :init-atoms :init-fns :goal-atoms :fluent-atoms :state-space :action-space)
  
(defn- get-instantiations [thing-map objects]
  (for [[n types] thing-map,
	args (apply util/cartesian-product (map #(util/safe-get objects %) types))]
    (vec (cons n args))))

(defn make-hybrid-strips-planning-instance
  ([name domain objects init-atoms init-fns goal-atoms]
     (make-hybrid-strips-planning-instance name domain objects init-atoms init-fns goal-atoms str nil))
  ([name domain objects init-atoms init-fns goal-atoms state-str-fn discrete-grid-size]
 ;    (println objects init-atoms init-fns goal-atoms)
     (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata equality?]} domain
	   discrete-type-map (into {} (map #(vector % nil) discrete-types))
	   objects (props/check-objects discrete-type-map objects)
	   object-type-map (into {} (for [[t os] objects, o os] [o t]))
	   all-atoms (set (get-instantiations predicates objects))]
       (doseq [nf-inst (get-instantiations numeric-functions objects)]
	 (when-not (number? (get init-fns nf-inst))
	   (println "Warning: No initial number for " nf-inst)))
;	 (util/assert-is (number? (get init-fns nf-inst))))
       (struct hybrid-strips-planning-instance ::HybridStripsPlanningInstance
	 name
	 domain
	 objects
	 (set 
	  (map #(check-atom % predicates object-type-map)
	      (concat init-atoms
		      (when equality? (for [[t os] objects, o os] [(util/symbol-cat t '=) o o])))))
	 init-fns
	 (set (map #(check-atom % predicates object-type-map) goal-atoms))
	 all-atoms
	 (make-hybrid-state-space all-atoms (util/keyset init-fns) state-str-fn)
	 (make-hybrid-action-space discrete-types objects action-schemata discrete-grid-size)))))



(defmethod envs/get-domain        ::HybridStripsPlanningInstance [instance]
  (util/safe-get instance :domain))

(defmethod envs/get-initial-state ::HybridStripsPlanningInstance [instance]
  (envs/metafy-initial-state [(:init-atoms instance) (:init-fns instance)]))

(defmethod envs/get-state-space   ::HybridStripsPlanningInstance [instance]
  (:state-space instance))

(defmethod envs/get-action-space  ::HybridStripsPlanningInstance [instance] 
  (:action-space instance))

(defmethod envs/get-goal          ::HybridStripsPlanningInstance [instance]
;  (println (:goal-atoms instance))
  (make-constraint-condition
   (make-conjunctive-constraint
    (map #(make-discrete-pos-constraint %) (:goal-atoms instance)))
   nil 
   nil))
;  (envs/make-conjunctive-condition (:goal-atoms instance) nil))

	   



