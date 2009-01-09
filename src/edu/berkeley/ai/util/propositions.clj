(ns edu.berkeley.ai.util.propositions
  (:refer-clojure)
  (:use edu.berkeley.ai.util clojure.contrib.seq-utils))

(defn get-subtypes "Return all subtypes of type, starting with itself." [types type]
  (when type
    (lazy-cons type 
	       (lazy-mapcat  (partial get-subtypes types) (safe-get types type)))))

(defn check-types [types]
  (let [type-map (map-map seq->vector-pair types)]
;    (prn type-map)
    (assert-is (= (count types) (count type-map)) "Duplicate type")
    (doseq [type (keys type-map)]
      (let [distinct? (distinct-elts? (get-subtypes type-map type))]
	(assert-is (identity distinct?) "Recursive type or duplicate inclusion %s" (take 100 (get-subtypes type-map type)))))
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



(defn- maximal-subtypes- [types t1 t2]
  (let [s1 (get-subtypes types t1)
	s2 (get-subtypes types t2)]
    (cond (includes? t1 s2) [t1]
	  (includes? t2 s1) [t2]
	  :else             (concat-elts 
			     (for [t1p (rest s1), t2p (rest s2)]
			       (maximal-subtypes- types t1p t2p))))))

(defn maximal-subtypes [types parents]
  (assert-is (not (empty? parents)))
  (reduce (fn [tl1 tl2] (reduce clojure.set/union
				(for [t1 tl1, t2 tl2]
				  (set (maximal-subtypes- types t1 t2)))))
	  (map hash-set parents)))


	  
(defn is-type? [types objects obj type]
  (or (includes? obj (get objects type))
      (some (partial is-type? types objects obj) (get types type))))

(defn check-type [types objects obj type]
  (assert-is (is-type? types objects obj type)))

(defn check-atom [types objects predicates atom]
;  (println types)
;  (dotimes [_ 10] (println atom))
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
  (when (seq conj)
    (if (= (first conj) 'and)
      (rest conj)
    (list conj))))

(defn parse-pddl-conjunction [conj]
  (let [[pos neg]
	(separate #(not= (first %) 'not) (pddl-conjunction->seq conj))]
    [pos (map (fn [term] (assert-is (= 2 (count term))) (second term)) neg)]))