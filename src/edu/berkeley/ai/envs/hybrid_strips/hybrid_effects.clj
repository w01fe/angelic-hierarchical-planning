(ns edu.berkeley.ai.envs.hybrid-strips.hybrid-effects
  (:use clojure.test  edu.berkeley.ai.util  )
  (:require [edu.berkeley.ai.util [propositions :as props] [intervals :as iv]
	     [hybrid :as hybrid] [linear-expressions :as le]]
	 	[edu.berkeley.ai.envs.hybrid-strips.hybrid-constraints :as hc]))



(defstruct hybrid-strips-assignment :class :form :expr)
(defn make-assignment [form expr]
  (struct hybrid-strips-assignment ::Assignment form expr))

(defn execute-assignment [assignment var-map numeric-vals old-numeric-vals]
  (assoc numeric-vals
    (props/simplify-atom var-map (:form assignment))
    (le/evaluate-hybrid-linear-expr (:expr assignment) var-map old-numeric-vals)))


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
	      (hybrid/check-hybrid-atom a predicates discrete-vars)))
     (doall (for [a deletes] 
	      (do (assert-is (= 2 (count a))) 
		  (hybrid/check-hybrid-atom (second a) predicates discrete-vars))))
     (doall (for [a assignments] 
	      (do (assert-is (= 3 (count a))) 
		  (make-assignment (hybrid/check-hybrid-atom (nth a 1) numeric-functions discrete-vars)
				   (le/parse-and-check-hybrid-linear-expression (nth a 2) discrete-vars numeric-vars numeric-functions))))))))
	 

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

