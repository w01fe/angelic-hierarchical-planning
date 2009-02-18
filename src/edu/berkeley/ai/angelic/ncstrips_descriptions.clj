(ns edu.berkeley.ai.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use edu.berkeley.ai.angelic)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util.propositions :as props]
            [edu.berkeley.ai.domains.strips :as strips]
            [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv]
	    [edu.berkeley.ai.search.smart-csps :as smart-csps])
  )

;;; NCStrips descriptions


(derive ::NCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)


;; Single conditional dffects


(defstruct ncstrips-effect-schema 
  :pos-preconditions :neg-preconditions :forall-preconditions
  :adds :deletes :forall-effects
  :possible-adds :possible-deletes :possible-forall-effects 
  :forall-cost :cost-fn)

(defn make-ncstrips-effect-schema [pos-preconditions neg-preconditions forall-preconditions
				   adds deletes forall-effects
				   possible-adds possible-deletes possible-forall-effects 
				   forall-cost cost-expr]
  (struct ncstrips-effect-schema 
	  pos-preconditions neg-preconditions forall-preconditions
	  adds deletes forall-effects
	  possible-adds possible-deletes possible-forall-effects
	  forall-cost cost-expr))

(defn- normalize-ncstrips-forall [types vars-and-objects predicates [args [pos-pre neg-pre] [pos-eff neg-eff]]]
 ; (println args pos-pre neg-pre pos-eff neg-eff)
  (let [vars-and-objects (props/check-objects types (concat vars-and-objects args))
	atom-checker (fn [atoms] (set (map #(props/check-atom types vars-and-objects predicates %) atoms)))]
    [args [(atom-checker pos-pre) (atom-checker neg-pre)] [(atom-checker pos-eff) (atom-checker neg-eff)]]))
    

(defn- normalize-ncstrips-effect-atoms [types vars-and-objects predicates effect]
 ; (prn "\n\n" effect "\n\n")
  (let [atom-checker (fn [atoms] (set (map #(props/check-atom types vars-and-objects predicates %) atoms)))]
    (apply make-ncstrips-effect-schema 
	   (concat (for [[f forall?] 
			 [[:pos-preconditions false]
			  [:neg-preconditions false]
			  [:forall-preconditions true]
			  [:adds false]
			  [:deletes false]
			  [:forall-effects true]
			  [:possible-adds false]
			  [:possible-deletes false]
			  [:possible-forall-effects true]]]
		     (let [thing (util/safe-get effect f)]
		       (if forall? 
			   (map #(normalize-ncstrips-forall types vars-and-objects predicates %) thing)
			 (atom-checker thing))))
		   [(when-let [fc (util/safe-get effect :forall-cost)] 
		      (normalize-ncstrips-forall types vars-and-objects predicates fc))]
		   [(util/safe-get effect :cost-fn)]))))
      

(defn- check-ncstrips-effect [types vars-and-objects predicates effect]
  ;(simplify-ncstrips-effect 
   (normalize-ncstrips-effect-atoms types vars-and-objects predicates effect))





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
		    [:optional [:cost-parameters ~cost-parameters]]
		    [:optional [:cost-precondition ~cost-precondition]]
		    [:cost-expr ~cost-expr]}
		  (util/partition-all 2 clause)]
       (let [[pos-pre neg-pre forall-pre] (props/parse-pddl-conjunction-forall pre),
	     [add     del     forall-eff] (props/parse-pddl-conjunction-forall eff),
	     [p-add   p-del   forall-p-eff] (props/parse-pddl-conjunction-forall poss),
	     cost-parameters (props/parse-typed-pddl-list cost-parameters)]
	 (when cost-precondition (util/assert-is (not (empty? cost-parameters))))
;	 (println cost-expr)
;	 (println (eval '*ns*))
	 (make-ncstrips-effect-schema 
	   pos-pre neg-pre forall-pre 
	   add del forall-eff
	   p-add p-del forall-p-eff 
	   (when cost-parameters [cost-parameters (props/parse-pddl-conjunction cost-precondition) [nil nil]])
	   (binding [*ns* (find-ns 'edu.berkeley.ai.angelic.ncstrips-descriptions)]
	      (eval `(fn ncstrips-cost-fn ~(vec (map second (concat vars cost-parameters))) ~cost-expr)))))))
   vars))

;   (parse-hierarchy "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse.hierarchy" (make-warehouse-strips-domain))


;; At this point, when we instantiate, we have to handle four sets of CSPs
;; For each, we would like to evaluate it now, if possible
;; But this requires that it is both non-const and non-co-referring with other vars - forget it for now
; Deal with everything when we ground it.

; Here, basic task will be to replace preconditions with CSP.
; TODO: Should also maybe constant-simplify preconds at some point, not needed now



(defn instantiate-ncstrips-forall-schema [[args [pos neg] body] vars instance]
  (let [trans-objects (util/safe-get instance :trans-objects)]
  ;   (println "futzing " args pos neg body vars        (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) args)
    [args
     (smart-csps/create-smart-csp pos neg 
       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) args)
       (:const-pred-map instance))
     body]))
       
	       

(defn- instantiate-ncstrips-effect-schema [effect vars instance]
  (let [pos-preconditions (util/to-set (:pos-preconditions effect)),
	neg-preconditions (util/to-set (:neg-preconditions effect)),
	adds              (util/difference (util/to-set (:adds effect)) pos-preconditions)
	deletes           (util/difference 
			   (util/difference (util/to-set (:deletes effect)) neg-preconditions)
			   adds)
	possible-adds     (util/difference (util/to-set (:possible-adds effect)) pos-preconditions)
	possible-deletes  (util/difference (util/to-set (:possible-deletes effect)) neg-preconditions)
	csp-maker         (fn [foralls] (doall (map #(instantiate-ncstrips-forall-schema % vars instance) foralls)))]
;    (prn adds deletes)
;    (util/assert-is (empty? (util/intersection adds deletes)))
    (util/assert-is (empty? (util/intersection (util/union adds deletes) (util/union possible-adds possible-deletes))))
    (when (empty? (util/intersection pos-preconditions neg-preconditions))
      (make-ncstrips-effect-schema
       pos-preconditions neg-preconditions (csp-maker (util/safe-get effect :forall-preconditions))
       adds              deletes           (csp-maker (util/safe-get effect :forall-effects))
       possible-adds     possible-deletes  (csp-maker (util/safe-get effect :possible-forall-effects))
       (when-let [fc (util/safe-get effect :forall-cost)] 
	 (instantiate-ncstrips-forall-schema fc vars instance))
       (util/safe-get effect :cost-fn)))))

(defmethod instantiate-description-schema ::NCStripsDescriptionSchema [desc instance]
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.domains.strips/StripsPlanningInstance))
  (assoc desc :effects (doall (map #(instantiate-ncstrips-effect-schema % (util/safe-get desc :vars) instance) 
				   (util/safe-get desc :effects)))))


;  (instantiate-hierarchy (parse-hierarchy "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse.hierarchy" (make-warehouse-strips-domain)) (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))


(defstruct ncstrips-effect 
  :pos-preconditions :neg-preconditions :precondition-fns 
  :adds :deletes :effect-fns
  :possible-adds :possible-deletes :possible-effect-fns
  :cost-fn)

(defn make-ncstrips-effect 
  [pos-preconditions neg-preconditions precondition-fns
   adds deletes effect-fns possible-adds 
   possible-deletes possible-effect-fns
   cost-fn]
  (struct ncstrips-effect 
     pos-preconditions neg-preconditions precondition-fns
     adds deletes effect-fns possible-adds 
     possible-deletes possible-effect-fns
     cost-fn))



;; Grounded NCStrips descriptions

(defstruct ncstrips-description :class :effects)

(defn- get-csp-results [csp pos neg var-map pred-maps]
  (for [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
    (let [final-map (merge var-map combo)
	  grounder #(props/simplify-atom final-map %)]
      [(map grounder pos) (map grounder neg)])))

; Make a function that takes pred-maps as arguments and returns grounded [pos neg]
(defn- ground-ncstrips-csp [[args csp [pos neg]] var-map]
  (if (smart-csps/smart-csp-const? csp)
      (let [results (get-csp-results csp pos neg var-map [[:dummy :dummy]])]
	(fn [pred-maps] results))
    (fn [pred-maps] (get-csp-results csp pos neg var-map pred-maps))))

(defn- ground-ncstrips-cost [forall cost-fn var-map hla-vars]
  (if (not forall)
      (let [result (apply cost-fn (map #(util/safe-get var-map (second %)) hla-vars))]
	(fn [pred-maps] result))
    (let [early-args (map #(util/safe-get var-map (second %)) hla-vars)
	  [args csp _] forall]
;      (println csp var-map hla-vars)
      (fn [pred-maps]
;	(println pred-maps)
        (apply max
	  (for [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
	    (let [final-map (merge combo var-map)]
	      (apply cost-fn (concat early-args (map #(util/safe-get final-map (second %)) args))))))))))
    

; TODO: this is still slow -- set accounts 10% of time! 
; TODO: is this definition of cost-expr sufficiently general?
; TODO: lazy eval cost somehow?
(defn- ground-ncstrips-effect-atoms [var-map effect hla-vars]
  (let [instantiator #(props/simplify-atom var-map %)]
    (apply make-ncstrips-effect 
      (concat (for [[f forall?] 
		         [[:pos-preconditions false]
			  [:neg-preconditions false]
			  [:forall-preconditions true]
			  [:adds false]
			  [:deletes false]
			  [:forall-effects true]
			  [:possible-adds false]
			  [:possible-deletes false]
			  [:possible-forall-effects true]]]
		(let [thing (util/safe-get effect f)]
		  (if forall? 
		      (map #(ground-ncstrips-csp % var-map) thing)
		    (set (map instantiator thing)))))
	      [(ground-ncstrips-cost (util/safe-get effect :forall-cost) (util/safe-get effect :cost-fn) var-map hla-vars)]))))


; TODO: put back simplification?  Or provide ground-and-constant-simplify method?
(defn- ground-ncstrips-effect [effect var-map hla-vars]
;  (simplify-ncstrips-effect
   (ground-ncstrips-effect-atoms var-map effect hla-vars))


(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
;	  (filter identity 
     (map #(ground-ncstrips-effect % var-map (:vars schema)) (:effects schema))))

  
; TODO: make more efficient
(defn- progress-effect-clause [effect clause]
;  (println "Progress " effect clause)
  (let [pos-pre (util/safe-get effect :pos-preconditions)
	neg-pre (util/safe-get effect :neg-preconditions)]
    (when (and (every? clause pos-pre)
	       (every? #(not (= :true (clause %))) neg-pre))
      (let [pred-maps (valuation->pred-maps (dsv/make-dnf-simple-valuation #{clause} 0))
	    [more-pos-pre more-neg-pre] (apply map concat [nil nil] (map #(% pred-maps) (util/safe-get effect :precondition-fns)))]
;	(println more-pos-pre more-neg-pre)
	(when (and (every? clause more-pos-pre)
		   (every? #(not (= :true (clause %))) more-neg-pre))
;	  (println "go")
	  (let [all-pos-pre   (concat more-pos-pre pos-pre)
		all-neg-pre   (concat more-neg-pre neg-pre)
		clause        (into (reduce dissoc clause all-neg-pre) (map #(vector % :true) all-pos-pre))
		[adds dels]   (apply map concat [(util/safe-get effect :adds) (util/safe-get effect :deletes)]
				     (map #(% pred-maps) (util/safe-get effect :effect-fns)))
		[padds pdels] (apply map concat [(util/safe-get effect :possible-adds) (util/safe-get effect :possible-deletes)]
				      (map #(% pred-maps) (util/safe-get effect :possible-effect-fns)))
		unks          (concat (filter #(not= :true (clause %)) padds)
				      (filter #(= :true (clause %))    pdels))]
	   [(into (reduce dissoc clause dels)
	      (concat (map #(vector % :true) adds)
		      (map #(vector % :unknown) unks)))
	     (- ((util/safe-get effect :cost-fn) pred-maps))]))))))

(defn- progress-ncstrips [val desc combiner]
;  (println "proggy " val combiner)
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







