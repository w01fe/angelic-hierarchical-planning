(ns edu.berkeley.ai.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use clojure.contrib.seq-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.util.propositions edu.berkeley.ai.angelic edu.berkeley.ai.angelic.dnf-simple-valuations)
  )

;;; NCStrips descriptions
; wow: calls to eval are expensive.  4x faster by precompiling eval!


(derive ::NCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)


;; Single conditional dffects

(defstruct ncstrips-effect :pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes :cost)

(defn make-ncstrips-effect [pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr]
  (struct ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr))


(defn- normalize-ncstrips-effect-atoms [types vars-and-objects predicates effect]
;  (prn "\n\n" effect "\n\n")
  (let [atom-checker (partial check-atom types vars-and-objects predicates)]
    (apply make-ncstrips-effect 
	   (concat (for [f [:pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes]]
		     (distinct (map atom-checker (safe-get effect f))))
		   [(:cost effect)]))))

(defn- simplify-ncstrips-effect [effect]
  (let [pos-preconditions (set (:pos-preconditions effect)),
	neg-preconditions (set (:neg-preconditions effect)),
	adds              (clojure.set/difference (set (:adds effect)) pos-preconditions)
	deletes           (clojure.set/difference 
			   (clojure.set/difference (set (:deletes effect)) neg-preconditions)
			   adds)
	possible-adds     (clojure.set/difference (set (:possible-adds effect)) pos-preconditions)
	possible-deletes  (clojure.set/difference (set (:possible-deletes effect)) neg-preconditions)]
;    (prn adds deletes)
;    (assert-is (empty? (clojure.set/intersection adds deletes)))
    (assert-is (empty? (clojure.set/intersection (clojure.set/union adds deletes) (clojure.set/union possible-adds possible-deletes))))
    (when (empty? (clojure.set/intersection pos-preconditions neg-preconditions))
      (make-ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes (:cost effect)))))
      

(defn- check-ncstrips-effect [types vars-and-objects predicates effect]
  (simplify-ncstrips-effect (normalize-ncstrips-effect-atoms types vars-and-objects predicates effect)))





;; Ungrounded NCStrips description schemata

(defstruct ncstrips-description-schema :class :effects :vars)

(defn make-ncstrips-description-schema [types vars-and-objects predicates effects vars]
  ; TODO: check mutual exclusion condition!objects
  (struct ncstrips-description-schema ::NCStripsDescriptionSchema (doall (filter identity (map (partial check-ncstrips-effect types vars-and-objects predicates) effects))) vars))

(defmethod parse-description :ncstrips [desc domain vars]  
  (assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (make-ncstrips-description-schema 
   (safe-get domain :types) 
   (check-objects (safe-get domain :types) (concat (safe-get domain :guaranteed-objs) vars)) 
   (safe-get domain :predicates)
   (for [clause (rest desc)]
     (match [#{[:optional [:precondition    [unquote pre]]]
	       [:optional [:effect          [unquote eff]]]
	       [:optional [:possible-effect [unquote poss]]]
	       [:cost-expr [unquote cost-expr]]}
	     (chunk 2 clause)]
       (let [[pos-pre neg-pre] (parse-pddl-conjunction pre),
	     [add     del    ] (parse-pddl-conjunction eff),
	     [p-add   p-del  ] (parse-pddl-conjunction poss)]
	 (make-ncstrips-effect pos-pre neg-pre add del p-add p-del
		   (eval `(fn ~(vec (map second vars)) ~cost-expr))))))
   vars))


(defmethod instantiate-description-schema ::NCStripsDescriptionSchema [desc inst]
  (assert-is (isa? (:class inst) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  desc)





;; Grounded NCStrips descriptions

(defstruct ncstrips-description :class :effects)



; TODO: is this definition of cost-expr sufficiently general?
(defn- instantiate-ncstrips-effect-atoms [var-map effect hla-vars]
  (let [instantiator (partial simplify-atom var-map)]
    (apply make-ncstrips-effect 
	   (concat (for [f [:pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes]]
		     (distinct (map instantiator (safe-get effect f))))
		   [(apply (:cost effect) (map #(safe-get var-map (second %)) hla-vars))]))))
;		   [(eval `(let ~(vec (concat-elts (map (fn [[k v]] [k `'~v]) var-map))) 
;				   ~(:cost effect)))]))))

(defn- instantiate-ncstrips-effect [effect var-map hla-vars]
  (simplify-ncstrips-effect
   (instantiate-ncstrips-effect-atoms var-map effect hla-vars)))


(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
	  (filter identity (map #(instantiate-ncstrips-effect % var-map (:vars schema)) (:effects schema)))))

  
; TODO: make more efficient
(defn- progress-effect-clause [effect clause]
  (when (and (every? clause (:pos-preconditions effect))
	     (every? #(not (= :true (clause %))) (:neg-preconditions effect)))
    (let [clause (apply merge (apply dissoc clause (:neg-preconditions effect)) (map #(vector % :true) (:pos-preconditions effect)))
	  adds    ;(concat (:pos-preconditions effect)
			  (:adds effect);)
	  deletes ;(concat (:neg-preconditions effect)
			  (:deletes effect);)
	  unks    (concat (filter #(not= :true (clause %)) (:possible-adds effect))
			  (filter #(= :true (clause %))    (:possible-deletes effect)))]
;      (prn adds deletes unks)
      [(apply merge (apply dissoc clause deletes)
	      (concat (map #(vector % :true) adds)
		      (map #(vector % :unknown) unks)))
       (- (:cost effect))])))

(defn- progress-ncstrips [val desc combiner]
  (let [results 
	(filter identity
	  (for [clause (:dnf val)
		effect (:effects desc)]
	    (progress-effect-clause effect clause)))]
;    (prn results)
    (make-dnf-simple-valuation 
     (map first results)
     (+ (:bound val) (reduce combiner (map second results))))))
      
(defmethod progress-optimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc]
  (progress-ncstrips val desc max))

(defmethod progress-pessimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc] ;TODO: improve
  (progress-ncstrips val desc min))






;(defmethod regress-optimistic (partial (map :class)))
;(defmethod regress-pessimistic (partial (map :class)))

