(ns edu.berkeley.ai.search.smart-csps
 (:use clojure.test )
 (:import [java.util HashMap Map ArrayList])
 (:require [edu.berkeley.ai.util :as util] 
	   [edu.berkeley.ai.util.propositions :as props]
	   [edu.berkeley.ai.envs :as envs]
	   )
 )

; TODO: look at pattern/production matching, ala soar, instead?
  ; Chapter 9 AIMA - benefit: incremental.

; For now,
 ; no guaranteed objects
 ; no multiple occurances of same var in pred

; Initial-domains ==> var --> vars to *sets* of values, or single values for args
; Vars-left       ==> Ordered seq of [var arg?] left to instantiate
; var-map         ==> var --> [pos-const neg-const pos-fluent neg-fluent]
; const-map       ==> constraint-name --> val-maps
; clause-maps     ==> (list constraint-name --> val-maps)
; inst-map        ==> dummy variables instantiated so far, with values

; Returns new-domain
; TODO: change to use keyset
(defn filter-pos-domain [#^HashMap map pred domain]
;  (println "fpd" map pred domain)
  (util/intersection-coll domain (if-let [#^Map m (first (.get map pred))] (.keySet m) nil)))

(defn filter-neg-domain [map pred domain]
;  (println map pred domain)
  (let [sub (first (get map pred))]
    (reduce (fn [domain val] (if (true? (get sub val)) (disj domain val) domain)) domain domain)))
;  (util/difference domain (util/keyset (get map pred {}))))

;(defn simplify-map [#^HashMap map preds val]
;  (if (empty? preds) map
;    (let [#^HashMap m (.clone map)]
;      (doseq [pred preds]
;        (.put m pred (get (.get m pred) val)))
;      m))) 

(defn simplify-map [#^HashMap map preds val]
;  (println "simpl" map preds val)
  (doseq [pred preds]
    (let [sub (.get map pred)
	  fs (first sub)]
      (.put map pred (cons (get fs val) sub)))))


(defn unsimplify-map [#^HashMap map preds val]
  (doseq [pred preds]
    (.put map pred (next (.get map pred)))))
;  (reduce (fn [map pred] (assoc map pred (get (get map pred) val)))
;	  map preds))


(defn- all-solutions [vars-left initial-domains var-map const-map clause-maps inst-map #^ArrayList results]
;  (println vars-left initial-domains var-map const-map clause-maps inst-map "\n\n")
  (if (empty? vars-left) (.add results inst-map);[inst-map]
    (let [[var arg?]    (first vars-left)
	  [pos-const neg-const pos-fluent neg-fluent] (util/safe-get var-map var)
	  const-domain 
	    (reduce (fn [domain nc] (filter-neg-domain const-map nc domain))
	        (reduce (fn [domain pc] (filter-pos-domain const-map pc domain))
	            (util/safe-get initial-domains var)
	          pos-const)
	      neg-const)
	  clause-domains
	    (map
             (fn [clause-map]
	       [clause-map
		(reduce (fn [domain nc] (filter-neg-domain clause-map nc domain))
	            (reduce (fn [domain pc] (filter-pos-domain clause-map pc domain))
	                const-domain
	              pos-fluent)
	          neg-fluent)])
	     clause-maps)
	  all-const (concat pos-const neg-const)
	  all-fluent (concat pos-fluent neg-fluent)
	    ]
;      (println clause-domains "\n\n\n\n")
;      (doall (util/forcat [val (apply util/union (map second clause-domains))]
      (doseq [val (apply util/union (map second clause-domains))]
	(let [rel-clause-maps (map first (filter #((second %) val) clause-domains))]
	  (when (next vars-left)
	    (simplify-map const-map all-const val)
	    (doseq [c rel-clause-maps] (simplify-map c all-fluent val)))
;	  (let [ret 
		(all-solutions 
		 (next vars-left)
		 initial-domains
		 var-map
		 const-map
		 rel-clause-maps
		 (if arg? inst-map (assoc inst-map var val)) results);]
	    (when (next vars-left)
	      (unsimplify-map const-map all-const val)
	      (doseq [c rel-clause-maps] (unsimplify-map c all-fluent val)))
	   ; ret
	    )))))
;	 (simplify-map const-map (concat pos-const neg-const) val)
;	 (map #(simplify-map % (concat pos-fluent neg-fluent) val) (map first (filter #((second %) val) clause-domains)))
;	 (if arg? inst-map (assoc inst-map var val)))))))


; pos-fluent and neg-fluent are just for prying eyes, like ground-strips-hierarhcy
(defstruct smart-csp :ordered-vars :unk-domains :var-pred-map :const-map :fluent-map-maker :unary-var :unary-val :pos-fluent :neg-fluent)


(defn get-smart-csp-solutions [csp var-values allowed-pred-inst-maps]
  (let [r (ArrayList.)]
  (all-solutions 
   (util/safe-get csp :ordered-vars)
   (assoc
       (reduce (fn [m [var val]] (assoc m var (hash-set val))) (util/safe-get csp :unk-domains) var-values)
     (:unary-var csp) (hash-set (:unary-val csp)))
   (util/safe-get csp :var-pred-map)
   (util/safe-get csp :const-map)
   (map (util/safe-get csp :fluent-map-maker) allowed-pred-inst-maps)
   {} r)
  (seq r)))



;; Little utils for making CSP

(defn fix-unaries [precs const-preds dummy-unary-var]
  (for [prec precs]
    (if (> (count prec) 1) prec
      (do (util/assert-is (not (const-preds (first prec))))
	  [(first prec) dummy-unary-var]))))

(defn fill-pred-map [atoms vars #^HashMap pred-names #^HashMap pred-instances]
  (util/merge-reduce concat {}
    (util/forcat [atom atoms]
      (let [pred-name (first atom)
	    gen-name  (gensym (name pred-name))
	    args      (next atom)]
	(util/assert-is (apply distinct? args))  ; For now.
	(doseq [arg args] (util/assert-is (vars arg)))
	(.put pred-names     pred-name (cons gen-name (.get pred-names pred-name)))
	(.put pred-instances gen-name  atom)
	(for [arg args] [arg [gen-name]])))))




;;;;;; Ordering vars

(defn expected-pred-prop [gen-pred pred-instances unk domain-size instantiated-set instance]
  (let [[pred & args] (get pred-instances gen-pred)]
;    (println pred args unk instantiated-set (util/position unk args) (for [[i v] (util/indexed args) :when (contains? instantiated-set v)] (inc i)))
    (/ (envs/expected-domain-size instance pred (inc (util/position unk args)) 
				  (for [[i v] (util/indexed args) :when (contains? instantiated-set v)] (inc i)))
       domain-size)))

(defn expected-domain-size-preds [unk all-domains var-pred-map pred-instances const-tuples instantiated-set instance]
  (let [[pos-const neg-const pos-fluent neg-fluent] (util/safe-get var-pred-map unk)
	domain-size (count (util/safe-get all-domains unk))]
 ;   (println "\n\n\n" unk pos-const neg-const pos-fluent neg-fluent)
    (if (= 0 domain-size) 0
      (* domain-size 
       (reduce * (map #(expected-pred-prop % pred-instances unk domain-size instantiated-set instance) 
		      (concat pos-const pos-fluent))) 
       (reduce * (map #(- 1 (expected-pred-prop % pred-instances unk domain-size instantiated-set instance)) 
		      (concat neg-const neg-fluent)))))))

(defn get-unk-ordering [unk-set all-domains var-pred-map pred-instances const-tuples instantiated-set unk-order instance]
  (if (empty? unk-set) unk-order
      (let [next
	      (util/first-maximal-element 
		(fn [unk] (- (expected-domain-size-preds unk all-domains var-pred-map pred-instances const-tuples instantiated-set instance)))
		unk-set)]
	(recur (disj unk-set next) all-domains var-pred-map pred-instances const-tuples (conj instantiated-set next) (conj unk-order next) instance))))

(defn get-var-ordering [args unks all-domains var-pred-map pred-instances const-tuples instance]
  (let [filterer (fn [vars] (set (remove (fn [var] (every? empty? (util/safe-get var-pred-map var))) vars)))
	args (filterer args)]
;	unks (filterer unks)]
;    (println "GVO " args unks var-pred-map)
    (concat (map #(vector % true)  args)
  	    (map #(vector % false) (get-unk-ordering unks all-domains var-pred-map pred-instances const-tuples args [] instance)))))



(defn get-permutation [args var-ordering]
  (let [arg-positions (map vector (iterate inc 1) (map #(util/position % var-ordering) args))]
    (vec (map first (sort-by second arg-positions)))))


(defn my-assoc-in [#^HashMap m #^clojure.lang.APersistentVector key-vec #^clojure.lang.APersistentVector perm ind]
;  (println m key-vec perm ind)
  (if (< (inc ind) (count perm))
      (let [key (.get key-vec (.get perm ind))
	    #^HashMap m2 
             (or (.get m key) 
		 (let [#^HashMap m2 (HashMap.)]
		   (.put m key m2)
		   m2))]
	(recur m2 key-vec perm (inc ind)))
    (.put m (.get key-vec (.get perm ind)) true)))

  
(defn make-value-map-maker "Take a set of allowed tuples and make a multi-stage map following the var-ordering."
  [pos? pred args var-ordering dummy-unary-var dummy-unary-val]
;  (println "val-map " args var-ordering allowed-tuples)
  (if (= (first args) dummy-unary-var) 
      (if pos?
	  (fn value-map-maker-unary1 [true-tuple-map poss-tuple-map] 
	    (when (or (seq (get true-tuple-map pred)) (seq (get poss-tuple-map pred))) {dummy-unary-val true}))
	(fn value-map-maker-unary2 [true-tuple-map poss-tuple-map] 
	  (when (seq (get true-tuple-map pred)) {dummy-unary-val true})))
    (let [permutation (get-permutation args var-ordering)]
      (if pos?
  	  (fn value-map-maker1 [true-tuple-map poss-tuple-map] 
	    (let [#^HashMap m (HashMap.)]
	      (doseq [tuple (concat (get true-tuple-map pred) (get poss-tuple-map pred))]
		(my-assoc-in m tuple permutation 0))
	      m))
;	    (reduce (fn [m t] (assoc-in m (permuter t) true)) {} (concat (get true-tuple-map pred) (get poss-tuple-map pred))))
	(fn value-map-maker2 [true-tuple-map poss-tuple-map] 
	  (let [#^HashMap m (HashMap.)]
	      (doseq [tuple (get true-tuple-map pred)]
		(my-assoc-in m tuple permutation 0))
	      m))))))
;	  (reduce (fn [m t] (assoc-in m (permuter t) true)) {} (get true-tuple-map pred)))))))

(defn make-value-pred-map-maker
  [pos-pred-name-map neg-pred-name-map pred-instance-map var-ordering dummy-unary-var dummy-unary-val]
;  (println "\n\n\n" "pred-map " pos-pred-name-map neg-pred-name-map pred-instance-map var-ordering true-tuple-map poss-tuple-map "n\n\n")
  (let [map-makers
	   (for [[pos? pred-name-map] [[true pos-pred-name-map] [false neg-pred-name-map]]
		 [pred pred-gens] pred-name-map
		 pred-gen pred-gens]
	     [pred-gen
	      (make-value-map-maker 
	       pos?
	       pred
	       (next (util/safe-get pred-instance-map pred-gen)) 
	       var-ordering
	       dummy-unary-var dummy-unary-val)])
	sz (count map-makers)
	bigsz (int (inc (* 1.12 sz)))]
    (fn pred-map-maker [[true-tuple-map poss-tuple-map]]
      (let [#^HashMap m (HashMap. bigsz 0.9)]
	(doseq [[pn map-maker] map-makers]
	  (.put m pn (list (map-maker true-tuple-map poss-tuple-map))))
	m))))
;      (HashMap.
;      (util/map-map
;       (fn [[pn map-maker]] [pn (map-maker true-tuple-map poss-tuple-map)])
;       map-makers)))))



  
;(defn dummy-fluent-unaries [tuple-map unary-val]
;  (doseq [unary unaries]
;    (when (seq (get tuple-map unary))
;      (.put tuple-map unary [[dummy-unary-val]]))) 

;  (reduce (fn [unary]
;	    (if (seq (get tuple-map unary))
;	      (assoc tuple-map unary [[dummy-unary-val]])
;	      tuple-map))
;	  tuple-map unaries))

(import '(java.util HashMap))
(defn create-smart-csp [pos-pre neg-pre arg-domains unk-domains const-pred-map instance]
 ; (println "Making CSP: " pos-pre neg-pre arg-domains unk-domains const-pred-map)
  (let [const-preds (util/keyset const-pred-map)
	dummy-unary-var (gensym "dummy-unary")
	dummy-unary-val (gensym "dummy-unary-val")
	arg-domains (assoc (util/map-vals set arg-domains) dummy-unary-var (hash-set dummy-unary-val))
	unk-domains (util/map-vals set unk-domains)
	const-preds (util/keyset const-pred-map)
;	unaries (set (map first (filter #(= (count %) 1) (concat pos-pre neg-pre))))
	pos-pre (fix-unaries pos-pre const-preds dummy-unary-var)
	neg-pre (fix-unaries neg-pre const-preds dummy-unary-var)
	[pos-const pos-fluent]   (util/separate #(const-preds (first %)) pos-pre)
	[neg-const neg-fluent] (util/separate #(const-preds (first %)) neg-pre)
	args (util/keyset arg-domains)
	unks (util/keyset unk-domains)
	vars (util/union args unks)
	pos-const-pred-names (HashMap.)     ; A map from real predicate names to seqs of gensym-names
	neg-const-pred-names (HashMap.)     ; A map from real predicate names to seqs of gensym-names
	pos-fluent-pred-names (HashMap.)     ; A map from real predicate names to seqs of gensym-names
	neg-fluent-pred-names (HashMap.)     ; A map from real predicate names to seqs of gensym-names
	pred-instances (HashMap.) ; A map from gensym-names to actual pred instances (non-gensym + seqs of vars)
	pos-const-map  (fill-pred-map pos-const vars pos-const-pred-names pred-instances)
	neg-const-map  (fill-pred-map neg-const vars neg-const-pred-names pred-instances)
	pos-fluent-map (fill-pred-map pos-fluent vars pos-fluent-pred-names pred-instances)
	neg-fluent-map (fill-pred-map neg-fluent vars neg-fluent-pred-names pred-instances)
;	pred-names (into {} pred-names)
	pred-instances (into {} pred-instances)
;	const-pred-names  (reduce dissoc pred-names (util/difference (util/keyset pred-names) const-preds))
;	fluent-pred-names (reduce dissoc pred-names const-preds)
	var-pred-map   (into {}
			 (map (fn [var] [var 
					 [(pos-const-map var)
					  (neg-const-map var)
					  (pos-fluent-map var)
					  (neg-fluent-map var)]])
			      vars))
	ordered-vars (get-var-ordering args unks (merge unk-domains arg-domains) var-pred-map pred-instances const-pred-map instance)
	var-ordering (vec (map first ordered-vars))]
 ;   (println "Var ordering: " var-ordering)
    (util/assert-is (empty? (util/intersection args unks)))
    (struct smart-csp 
      ordered-vars
      unk-domains
      var-pred-map
      ((make-value-pred-map-maker pos-const-pred-names neg-const-pred-names pred-instances var-ordering dummy-unary-var dummy-unary-val)
       [const-pred-map {}])
      (make-value-pred-map-maker pos-fluent-pred-names neg-fluent-pred-names pred-instances var-ordering dummy-unary-var dummy-unary-val)
      dummy-unary-var
      dummy-unary-val
      pos-fluent 
      neg-fluent
      )))

(defn smart-csp-pos-fluent-constraints [csp] (:pos-fluent csp))
(defn smart-csp-neg-fluent-constraints [csp] (:neg-fluent csp))
(defn smart-csp-const? [csp]
  (and (empty? (smart-csp-pos-fluent-constraints csp))
       (empty? (smart-csp-neg-fluent-constraints csp))))
       
(defmethod envs/expected-domain-size ::DummyEnv [env pred ind inst-ind] 1)
(def *dummy-env* {:class ::DummyEnv})

(require '[edu.berkeley.ai.angelic :as angelic])
(require '[edu.berkeley.ai.angelic.dnf-valuations :as dv] )

(deftest test-smart-csp
  (is 
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b]} #{['bap :a :b]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4}} 
			  {'boo '[[boo 1 3] [boo 1 4] [boo 2 3]] 'bap '[[bap 1 3]]} *dummy-env*)
	{:c 5}
	[[{} {}]]))
      #{{:a 1 :b 4} {:a 2 :b 3}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo] ['bee :a]} #{['bap]} 
			  {}
			  {:a #{1 2 3 4 5}}
			  {} *dummy-env*)
	{}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation 
	  {'{[boo] :unknown [bap] :unknown [bee 1] :unknown} 0 
	    '{[bee 1] :true [bee 2] :unknown [bee 3] :true} 0
	    '{[bap] :true [bee 2] :true [bee 3] :true [bee 4] :true} 0
	    '{[boo] :true [bap] :unknown [bee 5] :unknown} 0}))))
      #{{:a 1} {:a 5}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo] ['bee :a]} #{['bap]} 
			  {}
			  {:a #{1 2 3 4 5} :b #{7 8}}
			  {} *dummy-env*)
	{}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation
	  {'{[boo] :unknown [bap] :unknown [bee 1] :unknown}  0
	    '{[bee 1] :true [bee 2] :unknown [bee 3] :true} 0
	    '{[bap] :true [bee 2] :true [bee 3] :true [bee 4] :true} 0
	    '{[boo] :true [bap] :unknown [bee 5] :unknown} 0}
	  ))))
      #{{:a 1 :b 7} {:a 5 :b 7} {:a 1 :b 8} {:a 5 :b 8}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b] ['bee :a :d] ['box :d]} #{['bap :a :b] ['biz :a :b] ['bat :a :b :d]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4 5} :d #{4 5 6}} 
			  {'boo '[[boo 1 3] [boo 1 4] [boo 2 3] [boo 2 5] [boo 1 5]] 'bap '[[bap 1 3]]}
			  *dummy-env*)
	{:c 5}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation
	  {'{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 4] :true [box 5] :true [biz 1 5] :true [biz 2 5] :true [biz 1 4] :unknown [bat 1 5 4] :true} 0 
	    '{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 6] :unknown [biz 1 5] :unknown [biz 2 5] :true [biz 1 4] :unknown} 0}
	  ))))
      #{{:a 1 :b 4 :d 4} {:a 2 :b 3 :d 5} {:a 1 :b 4 :d 6} {:a 1 :b 5 :d 6}})))
      
		  



(comment

  
		 ; These should use vectors...    
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
  




(comment 

(defn expected-const-prop- [pred args arg-index const-tuples unk all-domains instantiated-set]
;  (println "ecp- " pred args arg-index const-tuples unk instantiated-set (all-domains unk))
  (cond (= arg-index (count args))
	  (let [unk-index (inc (util/position unk args))]
	    (count (distinct (map #(nth % unk-index) const-tuples))))
        (contains? instantiated-set (nth args arg-index))
          (apply util/mean
            (map (fn [dval] (expected-const-prop- pred args (inc arg-index) (filter #(= dval (nth % arg-index)) const-tuples)
						 unk all-domains instantiated-set))
		 (util/safe-get all-domains (nth args arg-index))))
;	        (= (nth args arg-index) unk)
        :else
	  (recur pred args (inc arg-index) 
		 (filter #(contains? (util/safe-get all-domains (nth args arg-index)) 
				     (nth % (inc arg-index))) 
			 const-tuples) 
		 unk all-domains instantiated-set)))

; Expected proportion of domain values not ruled out by gen-pred - sum over uninstantiated, avg over instantiated 
(defn expected-const-prop [gen-pred pred-instances const-tuple-map unk domain all-domains instantiated-set]
  (let [[pred & args] (get pred-instances gen-pred)]
;    (println gen-pred (get pred-instances gen-pred) (count (get const-tuple-map pred)))
;    (println gen-pred pred args)
    (/ (expected-const-prop- pred args 0 (util/safe-get const-tuple-map pred) unk all-domains instantiated-set)
       (count domain))))

; TODO: hints about # pred instantiations (e.g., (atx b x) is functional) -- for now, do something stupid.
(defn expected-fluent-prop [gen-pred pred-instances unk instantiated-set]
  (Math/pow 0.6 (inc (count (util/intersection instantiated-set (set (next (get pred-instances gen-pred))))))))
)