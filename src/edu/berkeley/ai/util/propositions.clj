(ns edu.berkeley.ai.util.propositions
  (:refer-clojure)
  (:use edu.berkeley.ai.util))

;;; Helpers for dealing with propositional domains and PDDL syntax

; types are maps from a type to the types it contains
; objects are maps from types to sets of objects (not yet transitive)
; predicates are maps from names to lists of types
; atoms are predicate applications

(defn get-subtypes "Return all subtypes of type, starting with itself." [types type]
  (when type
    (lazy-seq (cons type 
	       (lazy-mapcat  #(get-subtypes types %) (safe-get types type))))))

(defn check-types [types]
  (let [type-map (map-map seq->vector-pair types)]
;    (prn type-map)
    (assert-is (= (count types) (count type-map)) "Duplicate type %s" (str types))
    (doseq [type (keys type-map)]
      (let [distinct? (distinct-elts? (get-subtypes type-map type))]
	(assert-is (identity distinct?) "Recursive type or duplicate inclusion %s" (take 100 (get-subtypes type-map type)))))
    type-map))


(defn check-objects [types guaranteed-objs]
  (let [obj-map (reduce (fn [m [k & vs]] (assoc-cat m k (if (coll? (first vs)) (first vs) vs))) {} guaranteed-objs)]
    (doseq [k (keys obj-map)] (safe-get types k))
    (assert-is (distinct-elts? (apply concat (vals obj-map))))
    (map-vals set obj-map)))
;    obj-map))

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
    (cond (some #{t1} s2) [t1]
	  (some #{t2} s1) [t2]
	  :else             (concat-elts 
			     (for [t1p (next s1), t2p (next s2)]
			       (maximal-subtypes- types t1p t2p))))))

(defn maximal-subtypes [types parents]
  (assert-is (not (empty? parents)))
  (reduce (fn [tl1 tl2] (apply union
				(for [t1 tl1, t2 tl2]
				  (set (maximal-subtypes- types t1 t2)))))
	  (map hash-set parents)))
	  
(defn is-type? [types objects obj type]
 ; (prn types objects obj type)
  (or (contains? (to-set (get objects type)) obj)
      (some #(is-type? types objects obj %) (get types type))))

(defn check-type [types objects obj type]
  (assert-is (is-type? types objects obj type)))

(defn check-atom [types objects predicates atom]
  (let [[pred & args] atom,
	type-sig (safe-get predicates pred)]
    (assert-is (= (count args) (count type-sig)) "Wrong number of predicate args. %s" [args type-sig])
    (doseq [[obj type] (map vector args type-sig)]
      (check-type types objects obj type))
    (vec atom)))


(defn simplify-atom  [m #^clojure.lang.APersistentVector atom]
;  (print (class m))
  (reduce (fn [v item]
	    (conj v 
	      (if-let [e (find m item)]
		  (val e)
                item)))
	  [(.get atom 0)] (next atom)))

(defn single-simplify-atom [var obj atom]
  (simplify-atom (hash-map var obj) atom))    

;;; Misc


;;; PDDL domain parsing helpers 

(defn parse-typed-pddl-list [s]
  (when (seq s)
    (match [[~v - ~t ~@rst] s]
      (cons [t v]
	    (parse-typed-pddl-list rst)))))

(defn parse-pddl-predicate [pred]
  (cons (first pred) (map first (parse-typed-pddl-list (next pred)))))

(defn pddl-conjunction->seq [conj]
  (when (seq conj)
    (if (= (first conj) 'and)
      (next conj)
    (list conj))))

(defn parse-pddl-conjunction [conj]
  (let [[pos neg]
	(separate #(not= (first %) 'not) (pddl-conjunction->seq conj))]
    [pos (map (fn [term] (assert-is (= 2 (count term))) (second term)) neg)]))

(defn parse-pddl-conjunction-forall [conj]
  (let [{:keys [pos neg forall]}
	(group-by #(cond (= (first %) 'not) :neg (= (first %) 'forall) :forall :else :pos)
		  (pddl-conjunction->seq conj))]
    [pos 
     (map (fn [term] (assert-is (= 2 (count term))) (second term)) neg)
     (map (fn [[_ typed-list prec eff]]
	    [(parse-typed-pddl-list typed-list)
	     (parse-pddl-conjunction prec)
	     (parse-pddl-conjunction eff)])
	  forall)
     ]))