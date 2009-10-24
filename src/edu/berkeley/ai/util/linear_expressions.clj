; This file defines methods for handing linear (actually affine) expressions, represented as 
; maps from variable names to multipliers.  nil is a 'special' variable that will
; always be bound to one, for constant terms.  

(ns edu.berkeley.ai.util.linear-expressions
  (:use clojure.test  edu.berkeley.ai.util  )
  (:require [edu.berkeley.ai.util [propositions :as props] [intervals :as iv] [hybrid :as hybrid]]
	    [clojure.contrib.generic.arithmetic :as ga]
 ;           [clojure.contrib.generic.comparison :as gc]
            [clojure.contrib.generic.math-functions :as gm]))



;; TODO: allow intervals, etc? 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;               Main machinery for dealing with affine expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn map-linear-expr-vars 
  "le is a linear expression, and f is a map that will be applied to all non-nil
   vars in le, which can output a new variable name, numeric value, or assignment map.
   nil is interpreted as 'no change', so we can use maps; to map to constant nil, use
   1 instead.  If f maps each var to a matrix, implements matrix-vector product.  If 
   f maps each var to a number, implements dot product."
  [f le]
  (persistent!
   (reduce (fn [result [var mult]]
	     (let [new-var (f var)]
	       (cond (map? new-var)
  		       (reduce (fn [result [var inner-mult]]
				 (assoc! result var (+ (* mult inner-mult) (get result var 0))))
			       result new-var)
		     (number? new-var) 
                       (assoc! result nil (+ (* mult new-var) (get result nil 0)))
		     (nil? new-var)
		       (assoc! result var (+ mult (get result var 0)))
		     :else ;assume new var
		       (assoc! result new-var (+ mult (get result new-var 0))))))
	   (transient {nil (get le nil 0)}) (dissoc le nil))))

(def *last-expr* nil)
(defn evaluate-linear-expr 
  "Like map-linear-expr-vars, but enforces that the expression evaluates to a constant,
   which is returned.  Typically, f will map each var to a number, in which case this
   is like a dot product."
  [f le]
;  (def *last-expr* [f le])
  (let [result (merge {nil 0} (map-linear-expr-vars f le))]
    (assert (= (count result) 1))
    (get result nil)))

(defn map-linear-expr-vars-ga
  "Same as map-linear-expr-vars, but use generic arithmetic.  Assume maps with type
   metadata are generic numbers..."
  [f le]
  (persistent!
   (reduce (fn [result [var mult]]
	     (let [new-var (f var)]
	       (cond (and (map? new-var) (not (:type ^new-var)))
  		       (reduce (fn [result [var inner-mult]]
				 (assoc! result var (ga/+ (ga/* mult inner-mult) (get result var 0))))
			       result new-var)
		     (or (number? new-var) (map? new-var))
                       (assoc! result nil (ga/+ (ga/* mult new-var) (get result nil 0)))
		     (nil? new-var)
		       (assoc! result var (ga/+ mult (get result var 0)))
		     :else ;assume new var
		       (assoc! result new-var (ga/+ mult (get result new-var 0))))))
	   (transient {nil (get le nil 0)}) (dissoc le nil))))

(defn evaluate-linear-expr-ga
  "Same as evaluate-linear-expr, but use generic arithmetic."
  [f le]
  (let [result (merge {nil 0} (map-linear-expr-vars-ga f le))]
    (assert (= (count result) 1))
    (get result nil)))



(deftest test-map-linear-expression-vars 
  (is (= (map-linear-expr-vars
	  {:a 5 
	   :b {:f 2 :g 6 :h 9}
	   :c :f
	   :d {:f -1 :i 4 nil 1}
	   :x 17
	   nil 42}
	  {:a 1 :b 2 :c -3 :d 3 :e 4 :g -3 nil 14})
	 {:e 4 :f -2 :g 9 :h 18 :i 12 nil 22})))

(deftest test-evaluate-linear-expr 
  (is (= (evaluate-linear-expr {:a 1} {}) 0))
  (is (= (evaluate-linear-expr
	  {:a 5 :b -2 :c 5 :d {nil -7} :e -1 :g 1 nil 42}
	  {:a 1 :b 2 :c -3 :d 3 :e 4 :g -3 nil 14})
	 -28))
  (is (thrown? Exception 
	(evaluate-linear-expr
	  {:a 5 :b -2 :c 5 :d {nil -7} :e -1 nil 42}
	  {:a 1 :b 2 :c -3 :d 3 :e 4 :g -3 nil 14}))))




(defn simplify-linear-expr
  "le is a linear expression, possibly including abs value maps, and f is a map from 
   variables to linear expression subsitions or new variable names."
  [f le]
  (persistent!
   (reduce (fn [result [var mult]]
             (if (map? var)
                 (let [simplified-var (simplify-linear-expr f var)]
                   (if (and (= (count simplified-var) 1) (get simplified-var nil))
                       (assoc! result nil (+ (abs (get simplified-var nil)) (get result nil)))
                     (assoc! result simplified-var mult)))
               (let [new-var (f var)]
                 (cond (map? new-var)
                         (reduce (fn [result [var inner-mult]]
                                   (assoc! result var (+ (* mult inner-mult) (get result var 0))))
                                 result new-var)
                       (nil? new-var)
                         (assoc! result var (+ mult (get result var 0)))
                       :else 
                         (assoc! result new-var (+ mult (get result new-var 0)))
                       ;:else (throw (RuntimeException. "Bad value in simplify-linear-expr"))
                       ))))
	   (transient {nil (get le nil 0)}) (dissoc le nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;          Extracting normalized (in)equalities from affine expresisons.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- linear-expr-norm-scaling 
  "Take an expression without a constant term, and return a numeric scaling to 
   normalize it so that some canonical variable will have weight 1."
  [le]
  (assert (not (contains? le nil)))
  (/ 1 (val (first (sort-by #(str (key %)) le)))))

  
(defn linear-expr-eqz->normalized-inequality
  "Interpret le as an equality = 0, and return 
   Return [norm-expr bounds], where norm-expr is a normalized linear expr
   with no constant term, and bound are the corresponding bounds.
   Returns true/false if the inequality is trivially satisfied or not."
  [le]
  (let [c (get le nil 0)
	le (filter-map #(not (zero? (val %))) (dissoc le nil))]
    (if (empty? le) (= c 0)
      (let [m  (linear-expr-norm-scaling le)]
	[(map-vals #(* m %) le) [(* -1 c m) (* -1 c m)]]))))

(defn linear-expr-gez->normalized-inequality
  "Interpret le as an inequality >= 0, and return 
   Return [norm-expr bounds], where norm-expr is a normalized linear expr
   with no constant term, and bound are the corresponding bounds.
   Returns true/false if the inequality is trivially satisfied or not."
  [le strict?]
  (let [c (get le nil 0)
	le (filter-map #(not (zero? (val %))) (dissoc le nil))]
    (if (empty? le) ((if strict? > >=) c 0)
      (let [m  (linear-expr-norm-scaling le)]
	[(map-vals #(* m %) le) (if (< m 0) [nil (* -1 c m)] [(* -1 c m) nil])]))))

(defn linear-expr-lez->normalized-inequality
  "Interpret le as an inequality <= 0, and return 
   Return [norm-expr bounds], where norm-expr is a normalized linear expr
   with no constant term, and bound are the corresponding bounds.
   Returns true/false if the inequality is trivially satisfied or not."
  [le strict?]
  (let [c (get le nil 0)
	le (filter-map #(not (zero? (val %))) (dissoc le nil))]
    (if (empty? le) ((if strict? < <=) c 0)
      (let [m  (linear-expr-norm-scaling le)]
	[(map-vals #(* m %) le) (if (< m 0) [(* -1 c m) nil] [nil (* -1 c m)])])) ))


(deftest test-linear-expr-norm-scaling
  (is (= (linear-expr-norm-scaling {:a 4 :b 3}) (/ 1 4)))
  (is (= (linear-expr-norm-scaling {:a -7}) (/ 1 -7)))
  (is (thrown? Exception (linear-expr-norm-scaling {})))
  (is (thrown? Exception (linear-expr-norm-scaling {:a 3 nil 5}))))

(deftest test-linear-expr-inequalities 
  (is (= (linear-expr-eqz->normalized-inequality
	  {:a 5 :b 10 :c 0 nil -10})
	 [{:a 1 :b 2} [2 2]]))
  (is (= (linear-expr-eqz->normalized-inequality
	  {:a 5 :b 10})
	 [{:a 1 :b 2} [0 0]]))
  (is (= (map #(linear-expr-eqz->normalized-inequality %)
	      [{nil -1} {nil 0} {nil 1} {}])
	 [false true false true]))

  (is (= (linear-expr-gez->normalized-inequality
	  {:a 5 :b 10 :d 0 :e 0 nil -10} false)
	 [{:a 1 :b 2} [2 nil]]))
  (is (= (linear-expr-gez->normalized-inequality
	  {:a -5 :b 10 nil -10} false)
	 [{:a 1 :b -2} [nil -2]]))
  (is (= (map #(linear-expr-gez->normalized-inequality % false)
	      [{nil -1} {nil 0} {nil 1} {}])
	 [false true true true]))

  (is (= (linear-expr-lez->normalized-inequality
	  {:a 5 :b 10 :f 0 nil -10} false)
	 [{:a 1 :b 2} [nil 2]]))
  (is (= (linear-expr-lez->normalized-inequality
	  {:a -5 :b 10 nil -10} false)
	 [{:a 1 :b -2} [-2 nil]]))
  (is (= (map #(linear-expr-lez->normalized-inequality % false)
	      [{nil -1} {nil 0} {nil 1} {}])
	 [true true false true])))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                    Stuff useful for hybrid linear systems         
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here things are a bit tricky, since it may be the case that things are not 
;; actually linear until the values of constant numeric functions are known. 
;; For these cases, we will allow the value of a linear map to be a function,
;; which when called on a var-map and map from constant state variables to values,
;; must evaluate to a constant.  This imposes the requirement that 
;; before calling any of the above functions, we must know we have a grounded
;; (constant simplified) expression first.

; We will also allow absolute values; if a var is a map, we assume it's an absolute-value LM.
; We assume these will only be used in cost expressions, and don't implement them for inequalities.
;; Do we want min/max also?  What do we need to make a reasonable heuristic?  
;; Can always just hard-code it as numeric parameters.  But, we need a forall.  


(derive ::ContinuousMapState ::ContinuousState)
(defmulti evaluate-hybrid-var (fn [var cont-state] (type cont-state)))
(defmethod evaluate-hybrid-var ::ContinuousMapState [var cont-state] (safe-get cont-state var))
(defmethod evaluate-hybrid-var clojure.lang.IPersistentMap [var cont-state] (safe-get cont-state var))


(defn extract-singleton-var [expr]
  (when (= (count expr) 1)
    (let [[k v] (first expr)]
      (when (= v 1) k))))

(defn extract-constant [expr]
  (if (empty? expr) 0
      (and (= (count expr) 1)
	   (get expr nil))))


(defn ground-hybrid-linear-expr 
  "Assign all discrete variables and evaluate constants, producing a 
   concrete linear expression (poss. including abs valuats) in remaining 
   grounded state vars and parameters."
  [expr disc-var-map const-fns]
  (into {} 
    (for [[k v] expr]
      [(cond (map? k)  (ground-hybrid-linear-expr k disc-var-map const-fns)
             (coll? k) (props/simplify-atom disc-var-map k) 
             :else k)
       (if (number? v) v (v disc-var-map const-fns))])))
	     
(defn evaluate-grounded-hybrid-linear-expr 
  "Evaluate the expression given continuous parameters + state variables.  
   Assumes ground-hybrid-linear-expr has already been called."
  [expr cont-var-map cont-state]
  (evaluate-linear-expr 
   (fn [var] 
     (cond (map? var)  (abs (evaluate-grounded-hybrid-linear-expr var cont-var-map cont-state))
           (coll? var) (evaluate-hybrid-var var cont-state)
           :else       (safe-get cont-var-map var)))
   expr))

(defn evaluate-hybrid-linear-expr 
  "Ground and evaluate the expression."
  [expr var-map cont-state]
  (evaluate-grounded-hybrid-linear-expr 
   (ground-hybrid-linear-expr expr var-map cont-state)
   var-map cont-state))

(defn- combine [op vs]
  (if (every? number? vs) 
    (apply op vs)
    (fn [dvm cf]
      (apply op (for [v vs] (if (number? v) v (v dvm cf)))))))
 
(defn hybrid-linear-expr->grounded-lm [expr disc-var-map cont-var-map const-fns]
  (assert const-fns)
;  (println expr cont-var-map)
  (simplify-linear-expr cont-var-map (ground-hybrid-linear-expr expr disc-var-map const-fns)))

(defn parse-and-check-hybrid-linear-expression
  ([expr discrete-vars numeric-vars numeric-functions constant-numeric-functions]
     (parse-and-check-hybrid-linear-expression expr discrete-vars numeric-vars numeric-functions constant-numeric-functions false))
  ([expr discrete-vars numeric-vars numeric-functions constant-numeric-functions only-atomic-var?]
;     (println expr)
  (cond (number? expr) 
          {nil expr}
	(contains? numeric-vars expr)
	  {expr 1}
	(contains? constant-numeric-functions (first expr))
	  (let [checked (hybrid/check-hybrid-atom expr numeric-functions discrete-vars)]	   
	    {nil (fn const-evaluator [disc-var-map const-fns] 
		   (safe-get const-fns (props/simplify-atom disc-var-map checked)))})
        (contains? numeric-functions (first expr))
	  {(hybrid/check-hybrid-atom expr numeric-functions discrete-vars) 1}
        :else 
	  (let [[op & args] expr
		parsed-args (map #(parse-and-check-hybrid-linear-expression %
				    discrete-vars (when-not only-atomic-var?  numeric-vars) 
				    numeric-functions constant-numeric-functions false)
				 args)]
	    (condp = op
	      '+ (apply merge-all-with #(combine + %) parsed-args)
	      '- (apply merge-all-with #(combine + %) 
			    (cons (first parsed-args)
				  (map (fn [m] (map-vals #(if (number? %) (- %) 
							      (fn [x y] (- (% x y)))) m)) 
				       (next parsed-args))))
	      '* (let [[const-args var-args] (separate #(= (keys %) [nil]) parsed-args)
		       consts (map #(get % nil) const-args)
		       var-arg (or (first var-args) {nil 1})]
		   (assert (<= (count var-args) 1))
		   (map-vals #(combine * (cons % consts)) var-arg))
	      'abs (let [arg (safe-singleton parsed-args)]
		     (if (and (= (count arg) 1) (contains? arg nil))
		         {nil (abs  (first (vals arg)))}
		       {(safe-singleton parsed-args) 1})))))))


(deftest linear-exprs 
  (is (= (parse-and-check-hybrid-linear-expression 
	  '(- (* y 3) 1 (* 2 (+ x 5))) {} '#{x y} #{} #{})
	 '{x -2 y 3 nil -11 }))
  (is (thrown? Exception (parse-and-check-hybrid-linear-expression '(* x y) {} '#{x y} #{} #{})))
  (is (= (ground-hybrid-linear-expr 
          (parse-and-check-hybrid-linear-expression 
	   '(* [x a] [y b]) {'a 't1 'b 't2} {} '{x [t1] y [t2]} '#{x})
	  '{a aa b bb} '{[x aa] 12})
	 '{[y bb] 12}))
  (is (= (ground-hybrid-linear-expr 
          (parse-and-check-hybrid-linear-expression 
	   '(* (+ [x a] 3) (- [y b] [x a] 4)) {'a 't1 'b 't2} {} '{x [t1] y [t2]} '#{x})
	  '{a aa b bb} '{[x aa] 12})
	 '{[y bb] 15 nil -240}))
  (is (= 25
	 (evaluate-grounded-hybrid-linear-expr 
	  (ground-hybrid-linear-expr
	    (parse-and-check-hybrid-linear-expression 
	     '(+ (- c 2) [gt a b]) 
	     {'a 't1 'b 't2} {'c 'x} {'gt ['t1 't2]} #{})
	    {'a 'aa 'b 'bb} {})
	  {'c 12} {'[gt aa bb] 15})))
  (let [e (ground-hybrid-linear-expr 
           (parse-and-check-hybrid-linear-expression 
            '(+ 1 (* [x c] (+ 2 (abs (* (+ [x a] 3) (- [y b] [x a] 4)))))) {'a 't1 'c 't1 'b 't2} {} '{x [t1] y [t2]} '#{x})
           '{a aa b bb c cc} '{[x aa] 12 [x cc] 2})]
    (is (= e '{nil 5 {[y bb] 15 nil -240} 2}))
    (is (= 35 (evaluate-grounded-hybrid-linear-expr e {} '{[y bb] 15})))))				   

	  
(comment 
  (let [[op arity]   (safe-get {'* [ga/* 2] '+ [ga/+ 2] '- [ga/- 2] 'abs [gm/abs 1]} (first expr))]
	    (assert-is (= arity (count (next expr))) "%s" expr)
	    (make-linear-expression op 
	      (map #(parse-and-check-linear-expression % 
		     discrete-vars (when-not only-atomic-var?  linear-vars) linear-functions)
		   (next expr)))))

	  







