(ns edu.berkeley.ai.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use edu.berkeley.ai.angelic)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util.propositions :as props]
            [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv])
  )

;;; NCStrips descriptions


(derive ::NCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)


;; Single conditional dffects


(defstruct ncstrips-effect :pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes :cost)

(defn make-ncstrips-effect [pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr]
  (struct ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr))

(defn- normalize-ncstrips-effect-atoms [types vars-and-objects predicates effect]
;  (prn "\n\n" effect "\n\n")
  (let [atom-checker #(props/check-atom types vars-and-objects predicates %)]
    (apply make-ncstrips-effect 
	   (concat (for [f [:pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes]]
		     (distinct (map atom-checker (util/safe-get effect f))))
		   [(:cost effect)]))))

(defn- simplify-ncstrips-effect [effect]
  (let [pos-preconditions (util/to-set (:pos-preconditions effect)),
	neg-preconditions (util/to-set (:neg-preconditions effect)),
	adds              (util/difference (util/to-set (:adds effect)) pos-preconditions)
	deletes           (util/difference 
			   (util/difference (util/to-set (:deletes effect)) neg-preconditions)
			   adds)
	possible-adds     (util/difference (util/to-set (:possible-adds effect)) pos-preconditions)
	possible-deletes  (util/difference (util/to-set (:possible-deletes effect)) neg-preconditions)]
;    (prn adds deletes)
;    (util/assert-is (empty? (util/intersection adds deletes)))
    (util/assert-is (empty? (util/intersection (util/union adds deletes) (util/union possible-adds possible-deletes))))
    (when (empty? (util/intersection pos-preconditions neg-preconditions))
      (make-ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes (:cost effect)))))
      

(defn- check-ncstrips-effect [types vars-and-objects predicates effect]
  (simplify-ncstrips-effect (normalize-ncstrips-effect-atoms types vars-and-objects predicates effect)))





;; Ungrounded NCStrips description schemata

(defstruct ncstrips-description-schema :class :effects :vars)

(defn make-ncstrips-description-schema [types vars-and-objects predicates effects vars]
  ; TODO: check mutual exclusion condition!objects
  (struct ncstrips-description-schema ::NCStripsDescriptionSchema (doall (filter identity (map (partial check-ncstrips-effect types vars-and-objects predicates) effects))) vars))

(defmethod parse-description :ncstrips [desc domain vars]  
  (util/assert-is (isa? (:class domain) :edu.berkeley.ai.domains.strips/StripsPlanningDomain))
  (make-ncstrips-description-schema 
   (util/safe-get domain :types) 
   (props/check-objects (util/safe-get domain :types) (concat (util/safe-get domain :guaranteed-objs) vars)) 
   (util/safe-get domain :predicates)
   (for [clause (rest desc)]
     (util/match [#{[:optional [:precondition    ~pre]]
		    [:optional [:effect          ~eff]]
		    [:optional [:possible-effect ~poss]]
		    [:cost-expr ~cost-expr]}
		  (util/partition-all 2 clause)]
       (let [[pos-pre neg-pre forall-pre] (props/parse-pddl-conjunction-forall pre),
	     [add     del     forall-eff] (props/parse-pddl-conjunction-forall eff),
	     [p-add   p-del   forall-p-eff] (props/parse-pddl-conjunction-forall poss)]
;	 (println cost-expr)
;	 (println (eval '*ns*))
	 (make-ncstrips-effect pos-pre neg-pre add del p-add p-del
	    (binding [*ns* (find-ns 'edu.berkeley.ai.angelic.ncstrips-descriptions)]
	      (eval `(fn ~(vec (map second vars)) ~cost-expr)))))))
   vars))




;(defstruct ncstrips-effect :pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes :cost)

;(defn make-ncstrips-effect [pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr]
;  (struct ncstrips-effect pos-preconditions neg-preconditions adds deletes possible-adds possible-deletes cost-expr))

(defmethod instantiate-description-schema ::NCStripsDescriptionSchema [desc inst]
  (util/assert-is (isa? (:class inst) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  desc)





;; Grounded NCStrips descriptions

(defstruct ncstrips-description :class :effects)


; TODO: this is still slow -- set accounts 10% of time! 
; TODO: is this definition of cost-expr sufficiently general?
; TODO: lazy eval cost somehow?
(defn- instantiate-ncstrips-effect-atoms [var-map effect hla-vars]
  (let [instantiator #(props/simplify-atom var-map %)]
    (apply make-ncstrips-effect 
	   (concat (for [f [:pos-preconditions :neg-preconditions :adds :deletes :possible-adds :possible-deletes]]
		     (set (map instantiator (util/safe-get effect f))))
		   [(apply (:cost effect) (map #(util/safe-get var-map (second %)) hla-vars))]))))
;		   [(eval `(let ~(vec (concat-elts (map (fn [[k v]] [k `'~v]) var-map))) 
;				   ~(:cost effect)))]))))

; TODO: put back simplification?
(defn- instantiate-ncstrips-effect [effect var-map hla-vars]
;  (simplify-ncstrips-effect
   (instantiate-ncstrips-effect-atoms var-map effect hla-vars))


(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
;	  (filter identity 
     (map #(instantiate-ncstrips-effect % var-map (:vars schema)) (:effects schema))))

  
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
;    (println val desc combiner)
    (if results  
        (dsv/make-dnf-simple-valuation 
          (map first results)
	  (+ (:bound val) (reduce combiner (map second results))))
      (do (println "Warning: empty valuation being produced in progress-ncstrips") *pessimal-valuation*))
))
      
(defmethod progress-optimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc]
  (progress-ncstrips val desc max))

(defmethod progress-pessimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc] ;TODO: improve
  (progress-ncstrips val desc min))







