(ns angelic.old.envs.hybrid-strips.effects
  (:use clojure.test   )
  (:require [angelic.util :as util] 
	    [angelic.util [propositions :as props] [intervals :as iv]
	     [hybrid :as hybrid] [linear-expressions :as le]]
	 	[angelic.old.envs.hybrid-strips.constraints :as hc]))



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

;(defn ground-hybrid-effect [effect disc-var-map constant-numeric-vals]
;  (assoc effect 
;    :assignments (map (fn [ass] 
;			(assoc ass :expr (le/ground-hybrid-linear-expr (:expr ass) 
;					    disc-var-map constant-numeric-vals)))
;		      (:assignments effect))))

;(defn get-hybrid-effect-parts [e]
;  (map e [:adds :deletes :assignments]))

(defn execute-effect [effect var-map [discrete-atoms numeric-vals]]
  (let [simplifier (fn [atoms] (map #(props/simplify-atom var-map %) atoms))]
    [(reduce conj 
      (reduce disj discrete-atoms (simplifier (:deletes effect)))
      (simplifier (:adds effect)))
     (reduce (fn [nv ae] (execute-assignment ae var-map nv numeric-vals)) numeric-vals (:assignments effect))]))
 

(def *empty-effect* (make-effect nil nil nil))

(defn parse-and-check-effect [effect discrete-vars predicates numeric-vars numeric-functions const-numeric-fns]
  (let [effects (if (or (empty? effect) (= (first effect) 'and)) (next effect) (list effect))
	{:keys [adds deletes assignments]}
          (group-by (fn [[a]] (cond (= a '=) :assignments (= a 'not) :deletes :else :adds)) effects)]
;    (println adds deletes assignments)
    (make-effect 
     (doall (for [a adds] 
	      (hybrid/check-hybrid-atom a predicates discrete-vars)))
     (doall (for [a deletes] 
	      (do (util/assert-is (= 2 (count a))) 
		  (hybrid/check-hybrid-atom (second a) predicates discrete-vars))))
     (doall (for [a assignments] 
	      (do (util/assert-is (= 3 (count a))) 
		  (make-assignment (hybrid/check-hybrid-atom (nth a 1) numeric-functions discrete-vars)
				   (le/parse-and-check-hybrid-linear-expression (nth a 2) discrete-vars numeric-vars numeric-functions const-numeric-fns))))))))
	 

(defn effected-predicates [effect]
  (set (map first (concat (:adds effect) (:deletes effect)))))

(defn effected-functions [unparsed-effect]
  (set (map #(first (second %))
	    (filter #(= (first %) '=)
		    (if (or (empty? unparsed-effect) (= (first unparsed-effect) 'and)) 
		        (next unparsed-effect) (list unparsed-effect))))))

(defn get-hybrid-effect-info 
  "Return [simplified-adds simplified-deletes simplified-effect-map] where simplified-effect-map
   is a map from variables to linear maps specifying their new values"
  [effect disc-var-map num-var-map constant-fns]
  (let [{:keys [adds deletes assignments]} effect
	simplify (fn [atoms] (map #(props/simplify-atom disc-var-map %) atoms))]
    [(simplify adds)
     (simplify deletes)
     (util/map-map (fn [{:keys [form expr]}] 
		[(props/simplify-atom disc-var-map form)
		 (le/hybrid-linear-expr->grounded-lm expr disc-var-map num-var-map constant-fns)]) 
	      assignments)]))

(deftest effects
  (is
   (= ['#{[fee] [frob xv] [bar xv]} '{[fra] 17 [frax xv] 13 }]
      (execute-effect 
       (parse-and-check-effect '(and (fee) (frob x) (not (foo x)) (not (bar x)) (bar x) 
				     (= (fra) z) (= (frax x) (+ (frax x) (- (fra) 2)))) 
			       '{x xt} '{foo [xt] frob [xt] bar [xt] fee []} '{z zt} '{frax [xt] fra []} nil)
       '{x xv z 17} ['#{[foo xv] [bar xv]} '{[frax xv] 1 [fra] 14}]))))

