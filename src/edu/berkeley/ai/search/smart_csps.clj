(ns edu.berkeley.ai.search.smart-csps
 (:refer-clojure)
 (:require [edu.berkeley.ai.util :as util] 
	   [edu.berkeley.ai.util.propositions :as props]
	   )
 )

; TODO: Remove vars with no active constraints.
; TODO: order vars and constraints to put const first

; TODO: for now,
 ; no multi-occurances
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
(defn filter-pos-domain [map pred domain]
  (util/intersection-coll domain (keys (get map pred {}))))

;; TODO: make smarter?
(defn filter-neg-domain [map pred domain]
;  (println map pred domain)
   (reduce (fn [domain val] (if (true? (get (get map pred) val)) (disj domain val) domain)) domain domain))
;  (util/difference domain (util/keyset (get map pred {}))))

(defn simplify-map [map preds val]
  (reduce (fn [map pred] (assoc map pred (get (get map pred) val)))
	  map preds))


(defn- all-solutions [vars-left initial-domains var-map const-map clause-maps inst-map]
;  (println vars-left initial-domains var-map const-map clause-maps inst-map "\n\n")
  (if (empty? vars-left) [inst-map]
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
	     clause-maps)]
;      (println clause-domains "\n\n\n\n")
      (util/forcat [val (apply util/union (map second clause-domains))]
	(all-solutions 
	 (rest vars-left)
	 initial-domains
	 var-map
	 (simplify-map const-map (concat pos-const neg-const) val)
	 (map #(simplify-map % (concat pos-fluent neg-fluent) val) (map first (filter #((second %) val) clause-domains)))
	 (if arg? inst-map (assoc inst-map var val)))))))



(defstruct smart-csp :ordered-vars :unk-domains :var-pred-map :const-map :fluent-map-maker :unary-var :unary-val)

(defn get-smart-csp-solutions [csp var-values allowed-pred-inst-maps]
  (all-solutions 
   (util/safe-get csp :ordered-vars)
   (assoc
       (reduce (fn [m [var val]] (assoc m var (hash-set val))) (util/safe-get csp :unk-domains) var-values)
     (:unary-var csp) (hash-set (:unary-val csp)))
   (util/safe-get csp :var-pred-map)
   (util/safe-get csp :const-map)
   (map (util/safe-get csp :fluent-map-maker) allowed-pred-inst-maps)
   {}))



;; Little utils for making CSP

(defn fix-unaries [precs const-preds dummy-unary-var]
  (for [prec precs]
    (if (> (count prec) 1) prec
      (do (util/assert-is (not (const-preds (first prec))))
	  (list (first prec) dummy-unary-var)))))

(defn fill-pred-map [atoms vars #^HashMap pred-names #^HashMap pred-instances]
  (util/merge-reduce concat {}
    (util/forcat [atom atoms]
      (let [pred-name (first atom)
	    gen-name  (gensym (name pred-name))
	    args      (rest atom)]
	(util/assert-is (apply distinct? args))  ; For now.
	(doseq [arg args] (util/assert-is (vars arg)))
	(.put pred-names     pred-name (cons gen-name (.get pred-names pred-name)))
	(.put pred-instances gen-name  atom)
	(for [arg args] [arg [gen-name]])))))




;;;;;; Ordering vars

(defn expected-const-prop- [pred args arg-index const-tuples unk all-domains instantiated-set]
;  (println "ecp- " pred args arg-index const-tuples unk instantiated-set (all-domains unk))
  (cond (= arg-index (count args))
	  (let [unk-index (util/position unk args)]
	    (count (distinct (map #(nth % unk-index) const-tuples))))
        (contains? instantiated-set (nth args arg-index))
          (util/mean
            (map (fn [dval] (expected-const-prop- pred args (inc arg-index) (filter #(= dval (nth % arg-index)) const-tuples)
						 unk all-domains instantiated-set))
		 (util/safe-get all-domains (nth args arg-index))))
;	        (= (nth args arg-index) unk)
        :else
	  (recur pred args (inc arg-index) 
		 (filter #(contains? (util/safe-get all-domains (nth args arg-index)) 
				     (nth % arg-index)) 
			 const-tuples) 
		 unk all-domains instantiated-set)))

; Expected proportion of domain values not ruled out by gen-pred - sum over uninstantiated, avg over instantiated 
(defn expected-const-prop [gen-pred pred-instances const-tuple-map unk domain all-domains instantiated-set]
  (let [[pred & args] (get pred-instances gen-pred)]
;    (println gen-pred pred args)
    (/ (expected-const-prop- pred args 0 (util/safe-get const-tuple-map pred) unk all-domains instantiated-set)
       (count domain))))

; TODO: hints about # pred instantiations (e.g., (atx b x) is functional) -- for now, do something stupid.
(defn expected-fluent-prop [gen-pred pred-instances unk instantiated-set]
  (Math/pow 0.6 (inc (count (util/intersection instantiated-set (set (rest (get pred-instances gen-pred))))))))

(defn expected-domain-size [unk all-domains var-pred-map pred-instances const-tuples instantiated-set]
  (let [[pos-const neg-const pos-fluent neg-fluent] (util/safe-get var-pred-map unk)
	domain (util/safe-get all-domains unk)]
;    (println unk pos-const neg-const pos-fluent neg-fluent)
    (* (count domain)
       (reduce * (map #(expected-const-prop % pred-instances const-tuples unk domain all-domains instantiated-set) pos-const)) 
       (reduce * (map #(- 1 (expected-const-prop % pred-instances const-tuples unk domain all-domains instantiated-set)) neg-const))
       (reduce * (map #(expected-fluent-prop % pred-instances unk instantiated-set) pos-fluent))  
       (reduce * (map #(- 1 (expected-fluent-prop % pred-instances unk instantiated-set)) neg-fluent)))))  

(defn get-unk-ordering [unk-set all-domains var-pred-map pred-instances const-tuples instantiated-set unk-order]
  (if (empty? unk-set) unk-order
      (let [next
	      (util/first-maximal-element 
		(fn [unk] (- (expected-domain-size unk all-domains var-pred-map pred-instances const-tuples instantiated-set)))
		unk-set)]
	(recur (disj unk-set next) all-domains var-pred-map pred-instances const-tuples (conj instantiated-set next) (conj unk-order next)))))

(defn get-var-ordering [args unks all-domains var-pred-map pred-instances const-tuples]
  (concat (map #(vector % true)  args)
	  (map #(vector % false) (get-unk-ordering unks all-domains var-pred-map pred-instances const-tuples args []))))


;;; Making final maps.  TODO: precompile?
(defn make-permuter [args var-ordering]
  (let [arg-positions (map vector (iterate inc 0) (map #(util/position % var-ordering) args))
	arg-permutation (map first (sort-by second arg-positions))]
    (fn [tuple] (map #(nth tuple %) arg-permutation))))
   
;; TODO: filter based on domains?
(defn make-value-map "Take a set of allowed tuples and make a multi-stage map following the var-ordering."
  [args var-ordering dummy-unary-var dummy-unary-val allowed-tuples]
;  (println "val-map " args var-ordering allowed-tuples)
  (if (not= (first args) dummy-unary-var) ;; TODO
      (let [permuter (make-permuter args var-ordering)]
        (reduce #(assoc-in %1 (permuter %2) true) {} allowed-tuples))
    (when (seq allowed-tuples) {dummy-unary-val true})))

(import '(java.util HashMap))
(defn make-value-pred-map
  [pos-pred-name-map neg-pred-name-map pred-instance-map var-ordering true-tuple-map poss-tuple-map dummy-unary-var dummy-unary-val]
;  (println "\n\n\n" "pred-map " pos-pred-name-map neg-pred-name-map pred-instance-map var-ordering true-tuple-map poss-tuple-map "n\n\n")
  (into {}
    (for [[pos? pred-name-map] [[true pos-pred-name-map] [false neg-pred-name-map]]
	  [pred pred-gens] pred-name-map
	  pred-gen pred-gens]
      [pred-gen
       (make-value-map 
	(rest (util/safe-get pred-instance-map pred-gen)) 
	var-ordering
	dummy-unary-var dummy-unary-val
	(if pos? 
	    (concat (get true-tuple-map pred) (get poss-tuple-map pred))
	  (get true-tuple-map pred)))])))

  
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
(defn create-smart-csp [pos-pre neg-pre arg-domains unk-domains const-pred-map]
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
	ordered-vars (get-var-ordering args unks (merge unk-domains arg-domains) var-pred-map pred-instances const-pred-map)
	var-ordering (vec (map first ordered-vars))]
;    (println "Var pred map: " var-pred-map)
    (println "Var ordering: " var-ordering)
    (util/assert-is (empty? (util/intersection args unks)))
    (struct smart-csp 
      ordered-vars
      unk-domains
      var-pred-map
      (make-value-pred-map pos-const-pred-names neg-const-pred-names pred-instances var-ordering const-pred-map {} dummy-unary-var dummy-unary-val)
      (fn [[true-fluent-tuples poss-fluent-tuples]]
	(make-value-pred-map pos-fluent-pred-names neg-fluent-pred-names pred-instances var-ordering
			     true-fluent-tuples poss-fluent-tuples dummy-unary-var dummy-unary-val))
      dummy-unary-var
      dummy-unary-val)))

(require '[edu.berkeley.ai.angelic :as angelic])
(require '[edu.berkeley.ai.angelic.dnf-simple-valuations :as dnf-simple-valuations] )

(util/deftest test-smart-csp
  (util/is 
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b]} #{['bap :a :b]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4}} 
			  {'boo [[1 3] [1 4] [2 3]] 'bap [[1 3]]})
	{:c 5}
	[[{} {}]]))
      #{{:a 1 :b 4} {:a 2 :b 3}}))
  (util/is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo] ['bee :a]} #{['bap]} 
			  {}
			  {:a #{1 2 3 4 5}}
			  {})
	{}
	(angelic/valuation->pred-maps 
	 (dnf-simple-valuations/make-dnf-simple-valuation 
	  #{'{[boo] :unknown [bap] :unknown [bee 1] :unknown} 
	    '{[bee 1] :true [bee 2] :unknown [bee 3] :true}
	    '{[bap] :true [bee 2] :true [bee 3] :true [bee 4] :true}
	    '{[boo] :true [bap] :unknown [bee 5] :unknown}}
	  0))))
      #{{:a 1} {:a 5}}))
  (util/is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b] ['bee :a :d] ['box :d]} #{['bap :a :b] ['biz :a :b] ['bat :a :b :d]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4 5} :d #{4 5 6}} 
			  {'boo [[1 3] [1 4] [2 3] [2 5] [1 5]] 'bap [[1 3]]})
	{:c 5}
	(angelic/valuation->pred-maps 
	 (dnf-simple-valuations/make-dnf-simple-valuation 
	  #{'{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 4] :true [box 5] :true [biz 1 5] :true [biz 2 5] :true [biz 1 4] :unknown [bat 1 5 4] :true} 
	    '{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 6] :unknown [biz 1 5] :unknown [biz 2 5] :true [biz 1 4] :unknown}}
	  0))))
      #{{:a 1 :b 4 :d 4} {:a 2 :b 3 :d 5} {:a 1 :b 4 :d 6} {:a 1 :b 5 :d 6}})))
      
		  
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
  




