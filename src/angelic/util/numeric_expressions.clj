(ns angelic.util.numeric-expressions
  (:use clojure.test  angelic.util  )
  (:require [angelic.util [propositions :as props] [intervals :as iv] [hybrid :as hybrid]]
	    [clojure.contrib.generic.arithmetic :as ga]
 ;           [clojure.contrib.generic.comparison :as gc]
            [clojure.contrib.generic.math-functions :as gm]))

;; Not currently in use ...
;; Expressions

(derive ::ContinuousMapState ::ContinuousState)

(defmulti evaluate-numeric-expr
  "Evaluate the given numeric expression in continuous state cont-state, after applying
   the variable mappings in var-map.  A default implementation is provided for simple continuous
   states represented as a maps from variables to numeric values, with metadata ::ContinuousMapState."
  (fn [expr var-map cont-state] [(:class expr) (type cont-state)])) 


;; Defualt method.  TODO: remove.
(defmethod evaluate-numeric-expr :default [expr var-map cont-state]
  (let [cont-state (or cont-state {})]
    (assert-is (isa? (type cont-state) clojure.lang.IPersistentMap))
    (evaluate-numeric-expr expr var-map (vary-meta cont-state assoc :type ::ContinuousMapState))))



(defmulti ground-and-simplify-numeric-expr 
  "Simplify the expression given a set of constant-named numeric functions and mappings for these.
   By default, does nothing."
  (fn [expr var-map constant-numeric-fns numeric-vals] (:class expr)))

(defmethod ground-and-simplify-numeric-expr   ::Num [expr var-map constant-numeric-fns numeric-vals] expr)


;; A constant.
(derive ::NumConst ::Num)
(defstruct hybrid-strips-numeric-constant :class :constant)
(defn make-numeric-constant [constant]
;  (assert-is (number? constant))
  (struct hybrid-strips-numeric-constant ::NumConst constant))

(defmethod evaluate-numeric-expr [::NumConst ::ContinuousMapState] [expr var-map numeric-vals]
  (:constant expr))


;; A continuous parameter to an action.
(derive ::NumVar ::Num)
(defstruct hybrid-strips-numeric-var :class :var)
(defn make-numeric-var [var]
  (struct hybrid-strips-numeric-var ::NumVar var))

(defmethod evaluate-numeric-expr [::NumVar ::ContinuousState]  [expr var-map numeric-vals]
  (safe-get var-map (:var expr)))

(defmethod ground-and-simplify-numeric-expr   ::Num [expr var-map constant-numeric-fns cont-state]
  (assoc expr :var (safe-get var-map (:var expr))))



; An ungrounded form, i.e., var with unfilled arguments, e.g., (distance-to ?x)
; Arguments come from discrete action arguments.
(derive ::NumForm ::Num)
(defstruct hybrid-strips-numeric-form :class :form)
(defn make-numeric-form [form]
  (struct hybrid-strips-numeric-form ::NumForm form))

(defmethod evaluate-numeric-expr [::NumForm ::ContinuousMapState] [expr var-map numeric-vals]
  ;(println var-map)
  (safe-get numeric-vals (props/simplify-atom var-map (:form expr))))

(defmethod ground-and-simplify-numeric-expr   ::NumForm [expr var-map constant-numeric-fns cont-state]
  (if (contains? constant-numeric-fns (first (:form expr)))
      (make-numeric-constant (make-safe (iv/interval-point (evaluate-numeric-expr expr var-map cont-state))))
    (make-numeric-form (props/simplify-atom var-map (:form expr)))))



; An expression.  Currently limited to +/- constant in some settings (i.e., effects?)
(derive ::NumExpr ::Num)
(defstruct hybrid-strips-numeric-expression :class :op :args)
(defn make-numeric-expression [op args]
  (struct hybrid-strips-numeric-expression ::NumExpr op args))

(defmethod evaluate-numeric-expr [::NumExpr ::ContinuousMapState] [expr var-map numeric-vals]
  (apply (:op expr) (map #(evaluate-numeric-expr % var-map numeric-vals) (:args expr))))

(defmethod ground-and-simplify-numeric-expr   ::NumExpr [expr var-map constant-numeric-fns cont-state]
  (let [op (:op expr)
	args (map #(ground-and-simplify-numeric-expr % var-map constant-numeric-fns cont-state) (:args expr))]
    (if (every? #(isa? (:class %) ::NumConst) args)
        (make-numeric-constant (apply op (map :constant args)))
      (make-numeric-expression op args))))



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
	  (make-numeric-form (hybrid/check-hybrid-atom expr numeric-functions discrete-vars))
        :else 
	  (let [[op arity]   (safe-get {'* [ga/* 2] '+ [ga/+ 2] '- [ga/- 2] 'abs [gm/abs 1]} (first expr))]
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















(comment ;old stuff


(defmulti extract-numeric-expr-form-and-diff (fn [expr] (:class expr)))  
;(defmulti translate-numeric-expr-vars (fn [expr var-map] (:class expr))) 
(defmethod extract-numeric-expr-form-and-diff ::Num [expr]         (throw (UnsupportedOperationException.)))

;(defmethod translate-numeric-expr-vars        ::Num [expr var-map] expr) 

;(defmethod translate-numeric-expr-vars        ::NumVar [expr var-map] 
;  (make-numeric-var (safe-get var-map (:var expr)))) 



(defmethod extract-numeric-expr-form-and-diff ::NumForm [expr]         
  [expr 0])


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


)