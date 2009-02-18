(ns edu.berkeley.ai.search.csps
 (:refer-clojure)
 (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.propositions :as props])
 )

;;; CSP
; Nodes are dummy var values, one constraint per clause
; A dead-end is when a constraint has no instantiations
; idea: each constraint is a set of allowed instantiations (may be repeated) from clause
; each variable value has a link to the constraints it appears in

;Positive only
; each constraint is a set of possible atoms from the formula. (on ? x) - (on a b) (on c b)
; setting a value of a variable filters the list of clauses.
; if any list goes empty, backtrack

;Negative
; Negative constraint is a set of impossible atoms. Setting a value filters the list as before. 
; If set is nonempty (singleton) when fully grounded, backtrack.

; Individual constraints are sets of (dis)allowed clauses from the formula.

(defstruct conjunctive-csp-constraint :class :index-map :values)

(defn make-positive-cp-csp-constraint [index-map values]
  (struct conjunctive-csp-constraint ::PositiveCSPConstraint index-map values))

(defn make-negative-cp-csp-constraint [index-map values]
  (struct conjunctive-csp-constraint ::NegativeCSPConstraint index-map values))


(defmulti #^{:doc "Return a simplified constraint from var=val, or nil for inconsistency"}
  simplify-constraint (fn [constraint var val] (:class constraint)))

(defmethod simplify-constraint ::PositiveCSPConstraint [constraint var val]
  (let [index-map (:index-map constraint)
	index (get index-map var)]
    (when-let [new-values (filter #(= (nth % index) val) (:values constraint))]
      (make-positive-cp-csp-constraint index-map new-values))))

(defmethod simplify-constraint ::NegativeCSPConstraint [constraint var val]
  (let [index-map (:index-map constraint)
	index (get index-map var)
	new-values (filter #(= (nth % index) val) (:values constraint))
	new-index-map (dissoc index-map var)]
    (when-not (and new-values (empty? new-index-map))
      (make-negative-cp-csp-constraint new-index-map new-values))))


(defn make-pn-cp-csp-constraint [cp cn]
  {:class ::PNCSPConstraint :pos cp :neg cn})

(defmethod simplify-constraint ::PNCSPConstraint [constraint var val]
  (when-let [pos (simplify-constraint (:pos constraint) var val)]
    (when-let [neg (simplify-constraint (:neg constraint) var val)]
      (make-pn-cp-csp-constraint pos neg))))

(defmulti #^{:doc "Return a simplified constraint from var=val, or nil for inconsistency"}
  conjoin-constraints (fn [c1 c2] [(:class c1) (:class c2)]))
 
(defmethod conjoin-constraints [::PositiveCSPConstraint ::NegativeCSPConstraint] [pos neg]
  (make-pn-cp-csp-constraint pos neg))

(defmethod conjoin-constraints [::NegativeCSPConstraint ::PositiveCSPConstraint] [neg pos]
  (make-pn-cp-csp-constraint pos neg))

(defmethod conjoin-constraints [::PositiveCSPConstraint ::PositiveCSPConstraint] [p1 p2]
  (util/assert-is (= (:index-map p1) (:index-map p2)))
  (make-positive-cp-csp-constraint (:index-map p1) (util/intersection-coll (set (:values p1)) (:values p2))))

(defmethod conjoin-constraints [::NegativeCSPConstraint ::NegativeCSPConstraint] [n1 n2]
  (util/assert-is (= (:index-map n1) (:index-map n2)))
  (make-negative-cp-csp-constraint (:index-map n1) (util/union-coll (set (:values n1)) (:values n2))))

(defmethod conjoin-constraints [::PNCSPConstraint ::PositiveCSPConstraint] [c pos]
  (make-pn-cp-csp-constraint (conjoin-constraints (:pos c) pos) (:neg c)))

(defmethod conjoin-constraints [::PositiveCSPConstraint ::PNCSPConstraint ] [pos c]
  (make-pn-cp-csp-constraint (conjoin-constraints (:pos c) pos) (:neg c)))

(defmethod conjoin-constraints [::PNCSPConstraint ::NegativeCSPConstraint] [c neg]
  (make-pn-cp-csp-constraint (:pos c) (conjoin-constraints (:neg c) neg)))

(defmethod conjoin-constraints [::NegativeCSPConstraint ::PNCSPConstraint] [neg c]
  (make-pn-cp-csp-constraint (:pos c) (conjoin-constraints (:neg c) neg)))

(defmethod conjoin-constraints [::PNCSPConstraint ::PNCSPConstraint] [c1 c2]
  (make-pn-cp-csp-constraint (conjoin-constraints (:pos c1) (:pos c2)) (conjoin-constraints (:neg c1) (:neg c2))))

(defstruct conjunctive-propositional-csp :class :domains :var-set-map :constraints)

(defn- make-cp-csp [domains var-set-map constraints]
  (struct conjunctive-propositional-csp ::ConjunctivePropositionalCSP domains var-set-map constraints))


; TODO: all unary constraints should be resolved first, domains filtered? 


; Assume all non-variabilized atoms have been removed.
(defn- process-args "Get [ground-args-parser var-map var-set]" [var-domains args pos?]
  (let [var-set (util/intersection (set args) (util/keyset var-domains))
	vars (util/make-safe (sort var-set))
	all-inds (map #(util/positions % args) vars)
	inds (map first all-inds)
	dups (filter #(> (count %) 1) all-inds)
	tmpl (map #(or (get var-domains %) %) args)]
;    (prn args pos? vars all-inds inds dups tmpl)
    [(fn [ground-args truth-val]
 ;      (util/prln "\n" ground-args truth-val "\n")
       (when (and (or pos? (= truth-val :true))
		  (util/mevery? (fn [t g] (if (set? t) (contains? t g) (= t g))) tmpl ground-args)
		  (every? (fn [l] (apply = (map #(nth ground-args %) l))) dups)) 
	   (vec (map #(nth ground-args %) inds))))
     (util/map-map vector vars (iterate inc 0))
     var-set]))
  

; TODO: split into csp-domains and instances, move much of pre-work to domains.  Domains should be sets!
(defn make-conjunctive-propositional-csp [domains pos-atoms neg-atoms ground-clause-map]
 ; (println domains pos-atoms neg-atoms ground-clause-map)
  (let [domains (util/map-map (fn [[k v]] [k (set v)]) domains)
	pred-map
	 (loop [pred-map  ; create map from predicates to lists of (value-set [p-fn var-map var-set] pos?) entries
		(util/merge-reduce concat {} 
		  (map (fn [atom] [(first atom) [(list #{} (process-args domains (rest atom) true) true)]]) pos-atoms)
		  (map (fn [atom] [(first atom) [(list #{} (process-args domains (rest atom) false) false)]]) neg-atoms))
		grounds (seq ground-clause-map)]
;	   (prn pred-map)
	   (if (empty? grounds) pred-map  ; process ground clauses into this map, checking against allowed domain values
	     (recur (let [[[pred & args] truth-val] (first grounds)]
		      (if-let [constraints (get pred-map pred) ]
			  (assoc pred-map pred
			         (for [elt constraints]
				   (let [[value-set [parse-fn]] elt]
				     (if-let [val-vec  (parse-fn args pos?)] 
					          ; (util/prln (parse-fn args truth-val) (cons pred args) elt)]
				         (cons (conj value-set val-vec)
					       (rest elt))
				       elt))))
		        pred-map))
		    (rest grounds))))
	set-map          ; create constraints and merge them, intersecting domains of pos constraints and unioning neg.
	  (util/merge-reduce conjoin-constraints {}
	    (mapcat (fn [[pred constraint-specs]]
		      (for [[vals [p-fn var-map var-set] pos?] constraint-specs]
		        ;(util/prln "AAA" pred vals p-fn var-map var-set pos?)
			[var-set ((if pos? make-positive-cp-csp-constraint make-negative-cp-csp-constraint)
				  var-map vals)]))
		    pred-map))]
    (make-cp-csp 
     domains
     (util/merge-reduce concat {} (mapcat (fn [s] (for [item s] [item [s]])) (keys set-map)))
     set-map)))


(defn set-variable-value "Return simplified CSP or nil for backtrack" [csp var val]
  (let [var-set-map (:var-set-map csp)]
    (when-let [new-constraints
	       (loop [all-sets (seq (get var-set-map var)),
		      new-constraints (:constraints csp)]
		 (if (empty? all-sets) new-constraints
		   (when-let [new-constraint 
			      (simplify-constraint (get new-constraints (first all-sets)) var val)]
		     (recur (rest all-sets)
			    (assoc new-constraints (first all-sets) new-constraint)))))]
      (make-cp-csp (assoc (:domains csp) var val) var-set-map new-constraints))))

(defn- all-csp-solutions-  [csp var-domains]
;  (prn csp var-domains)
  (if (empty? var-domains)
      [(:domains csp)]
    (util/lazy-mapcat #(when-let [next-csp (set-variable-value csp (ffirst var-domains) %)]
		    (all-csp-solutions- next-csp (rest var-domains)))
		 (second (first var-domains)))))

; TODO: improve?
(defn all-csp-solutions "For now, braindead depth-first search with no heuristics. Returns a lazy seq of solutions" [csp]
  (all-csp-solutions- csp (seq (:domains csp))))
		  
(comment 
  (all-csp-solutions 
   (make-conjunctive-propositional-csp 
    {:a #{1 2 3} :b #{4 5}} 
    '[[pop :a :b] [boop 2 :a] [bap :a :b]] 
    '[[pod :b :a]] 
    '{(boop 2 2) :true, (boop 2 3) :true, (bap 3 5) :true, (bap 2 4) :true, (pop 2 4) :true, (pop 2 5) :true, (pop 2 3) :true, (pod 4 3) :true}))

(all-csp-solutions 
   (make-conjunctive-propositional-csp 
    {:a #{1 2 3} :b #{4 5}} 
    '[[pop :a :b] [boop 2 :a] [bap :a :b] [bap :b 4]] 
    '[[pod :b :a]] 
    '{(boop 2 2) :true, (boop 2 3) :true, (bap 3 5) :true, (bap 2 4) :true, (bap 4 4) :true, (pop 2 4) :true, (pop 2 5) :true, (pop 3 5) :true, (pod 5 2) :true}))
 )
  




