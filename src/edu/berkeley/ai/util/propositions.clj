(ns edu.berkeley.ai.util.propositions
  (:refer-clojure)
  (:use edu.berkeley.ai.util clojure.contrib.seq-utils))

(defn check-types [types]
  (let [type-map (map-map seq->vector-pair types)]
    (assert-is (= (count types) (count type-map)) "Duplicate type")
    (loop [type-map type-map]
      (let [next-type-map 
	    (map-map 
	     (fn [[k vs]] 
	       [k (mapcat 
		   (fn [v] 
		     (assert-is (not= k v) "Recursion detected") 
		     (or (safe-get type-map v) [v])) 
		   vs)]) 
	     type-map)]
	(if (= next-type-map type-map) type-map
	    (do (doseq [[k vs] next-type-map]
		  (assert-is (distinct-elts? vs) "Duplicate inclusion"))
		(recur next-type-map)))))
    type-map))

(defn check-objects [types guaranteed-objs]
  (let [obj-map (reduce (fn [m [k & vs]] (assoc-cat m k (if (coll? (first vs)) (first vs) vs))) {} guaranteed-objs)]
    (doseq [k (keys obj-map)] (safe-get types k))
    (assert-is (distinct-elts? (apply concat (vals obj-map))))
    obj-map))


(defn check-predicates [types predicates]
  (let [pred-map (map-map seq->vector-pair predicates)]
    (assert-is (= (count predicates) (count pred-map)) "Duplicate predicate")
    (doseq [[pred pred-types] pred-map,
	    pred-type pred-types]
      (safe-get types pred-type))
    pred-map))

(defn get-subtypes [types type]
  (when type
    (cons type 
	  (map get-subtypes (safe-get types type)))))
	  
(defn is-type? [types objects obj type]
  (or (includes? obj (get objects type))
      (some (partial is-type? types objects obj) (get types type))))

(defn check-type [types objects obj type]
  (assert-is (is-type? types objects obj type)))

(defn check-atom [types objects predicates atom]
  (let [[pred & args] atom,
	type-sig (safe-get predicates pred)]
    (assert-is (= (count args) (count type-sig)) "Wrong number of predicate args.")
    (doseq [[obj type] (map vector args type-sig)]
      (check-type types objects obj type))
    (seq atom)))

(defn simplify-atom 
  ([var obj atom] (simplify-atom {var obj} atom))
  ([m atom]       (cons (first atom) (replace m (rest atom)))))
    
;;; PDDL domain parsing helpers 

(defn parse-typed-pddl-list [s]
  (when (seq s)
    (match [[[unquote v] - [unquote t] [unquote-seq rst]] s]
      (cons [t v]
	    (parse-typed-pddl-list rst)))))

(defn parse-pddl-predicate [pred]
  (cons (first pred) (map first (parse-typed-pddl-list (rest pred)))))

(defn pddl-conjunction->seq [conj]
  (if (= (first conj) 'and)
      (rest conj)
    (list conj)))

