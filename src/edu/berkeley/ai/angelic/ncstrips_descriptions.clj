(ns edu.berkeley.ai.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use clojure.contrib.seq-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.util.propositions edu.berkeley.ai.angelic)
  )


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
	deletes           (clojure.set/difference (set (:deletes effect)) neg-preconditions)
	possible-adds     (clojure.set/difference (set (:possible-adds effect)) pos-preconditions)
	possible-deletes  (clojure.set/difference (set (:possible-deletes effect)) neg-preconditions)]
    (assert-is (empty? (clojure.set/intersection adds deletes)))
    (assert-is (empty? (clojure.set/intersection (clojure.set/union adds deletes) (clojure.set/union possible-adds possible-deletes))))
    (when (empty? (clojure.set/intersection pos-preconditions neg-preconditions))
      (make-ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes (:cost effect)))))
      

(defn- check-ncstrips-effect [types vars-and-objects predicates effect]
  (filter identity (simplify-ncstrips-effect (normalize-ncstrips-effect-atoms types vars-and-objects predicates effect))))
  

(defn- instantiate-ncstrips-effect-atoms [var-map effect]
  (let [instantiator (partial simplify-atom var-map)]
    (apply make-ncstrips-effect 
	   (concat (for [f :pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes]
		     (distinct (map instantiator (safe-get effect f))))
		   [(eval `(fn ~(vec var-map) ~effect))]))))

(defn- instantiate-ncstrips-effect [effect var-map]
  (filter identity 
	  (simplify-ncstrips-effect
	   (instantiate-ncstrips-effect-atoms var-map effect))))


(defstruct ncstrips-description-schema :class :effects)

(defn make-ncstrips-description-schema [types vars-and-objects predicates effects]
  ; TODO: check mutual exclusion condition!objects
;  (prn effects) 
  (struct ncstrips-description-schema ::NCStripsDescriptionSchema (map (partial check-ncstrips-effect types vars-and-objects predicates) effects)))


(defmethod instantiate-description-schema ::NCStripsDescriptionSchema [desc inst]
  (assert-is (isa? (:class inst) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  desc)


(defstruct ncstrips-description :class :effects)

(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
	  (map #(instantiate-ncstrips-effect % var-map))))
  

  
(defn- progress-effect-clause [effect clause]
  (when (and (every? clause (:pos-preconditions effect))
	     (every? #(not (= :true (clause %))) (:neg-preconditions effect)))
    (let [adds    (concat (:pos-preconditions effect)
			  (:adds effect))
	  deletes (concat (:neg-preconditions effect)
			  (:deletes effect))
	  unks    (concat (remove clause (:possible-adds effect))
			  (filter #(= :true (clause %)) (:possible-deletes effect)))]
      (apply assoc (apply dissoc clause deletes)
	     (concat (interleave adds (repeat :true))
		     (interleave unks (repeat :unknown)))))))

(defn- progress-ncstrips [val desc combiner]
  (let [results 
	(for [clause (:dnf val)
	      effect (:effects desc)]
	  (progress-effect-clause effect clause))]
    (make-dnf-simple-valuation 
     (filter identity (distinct (map first results)))
     (reduce combiner (map second results)))))
      

(defmethod progress-optimistic [::DNFSimpleValuation ::NCSTRIPSDescription] [val desc]
  (progress-ncstrips val desc max))

(defmethod progress-pessimistic [::DNFSimpleValuation ::NCSTRIPSDescription] [val desc] ;TODO: improve
  (progress-ncstrips val desc min))


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
	 (make-ncstrips-effect pos-pre neg-pre add del p-add p-del cost-expr))))))


;(defmethod regress-optimistic (partial (map :class)))
;(defmethod regress-pessimistic (partial (map :class)))

