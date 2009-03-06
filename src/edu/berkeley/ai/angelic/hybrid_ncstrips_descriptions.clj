(ns edu.berkeley.ai.angelic.hybrid-ncstrips-descriptions
  (:refer-clojure)
  (:use edu.berkeley.ai.angelic)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid]]
            [edu.berkeley.ai.domains.hybrid-strips :as hs]
            [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv]
	    [edu.berkeley.ai.search.smart-csps :as smart-csps])
  )

;;; NCStrips descriptions


;; Effect schemata

(defstruct hybrid-ncstrips-effect-schema :precondition :effect :possible-effect :cost-epxr)

(defn make-hybrid-ncstrips-effect-schema [precondition effect possible-effect cost-expr]
  (struct hybrid-ncstrips-effect-schema precondition effect possible-effect cost-expr))

(defn parse-hybrid-ncstrips-effect-schema [effect discrete-vars predicates numeric-vars numeric-fns]
;  (println effect)
  (util/match [#{[:optional [:precondition    ~pre]]
		 [:optional [:effect          ~eff]]
		 [:optional [:possible-effect ~poss]]
		 [:cost-expr ~cost-expr]}
	       (util/partition-all 2 effect)]
    (util/assert-is (empty? poss))
    (make-hybrid-ncstrips-effect-schema
     (hybrid/parse-and-check-constraint pre discrete-vars predicates numeric-vars numeric-fns)
     (hybrid/parse-and-check-effect eff discrete-vars predicates numeric-vars numeric-fns)
     (hybrid/parse-and-check-effect poss discrete-vars predicates numeric-vars numeric-fns)
     (hybrid/parse-and-check-numeric-expression cost-expr discrete-vars numeric-vars numeric-fns))))
     

;; Description schemata



(defstruct hybrid-ncstrips-description-schema :class :discrete-vars :numeric-vars  :effects)
(defn make-hybrid-ncstrips-description-schema [discrete-vars numeric-vars effects]
    (struct hybrid-ncstrips-description-schema ::HybridNCStripsDescriptionSchema 
	    discrete-vars numeric-vars effects))

(defmethod parse-description :hybrid-ncstrips [desc domain vars]  
  (util/assert-is (isa? (:class domain) ::hs/HybridStripsPlanningDomain))
  (let [{:keys [discrete-types numeric-types predicates numeric-functions]} domain
	[discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)]
    (make-hybrid-ncstrips-description-schema discrete-vars numeric-vars
      (doall (map #(parse-hybrid-ncstrips-effect-schema % discrete-vars predicates numeric-vars numeric-functions) (next desc))))))





(derive ::HybridNCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)


(comment





;; Ungrounded NCStrips description schemata

(defstruct ncstrips-description-schema :class :effects :vars)

(defn make-ncstrips-description-schema [types vars-and-objects predicates effects vars]
  ; TODO: check mutual exclusion condition!objects
  (struct ncstrips-description-schema ::NCStripsDescriptionSchema (doall (filter identity (map (partial check-ncstrips-effect types vars-and-objects predicates) effects))) vars))



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

(import '(java.util ArrayList))
(defn- get-csp-results [csp pos neg var-map pred-maps]
  (let [pl (ArrayList.), nl (ArrayList.)]
    (doseq [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
      (let [final-map (merge var-map combo)  
  	    grounder #(props/simplify-atom final-map %)]
	(doseq [p pos] (.add pl (grounder p)))
	(doseq [n neg] (.add nl (grounder n)))))
    [(seq pl) (seq nl)]))
;      [(map grounder pos) (map grounder neg)])))

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
        (reduce max  ;; TODO???
	  (for [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
	    (let [final-map (merge combo var-map)]
	      (apply cost-fn (concat early-args (map #(util/safe-get final-map (second %)) args))))))))))
    

; TODO: this is still slow -- set accounts 10% of time! 
; TODO: is this definition of cost-expr sufficiently general?
; TODO: lazy eval cost somehow? (no set)?
(defn- ground-ncstrips-effect-atoms [var-map effect hla-vars]
  (let [instantiator #(props/simplify-atom var-map %)]
    (make-ncstrips-effect 
     (map instantiator (util/safe-get effect :pos-preconditions))
     (map instantiator (util/safe-get effect :neg-preconditions))
     (map #(ground-ncstrips-csp % var-map) (util/safe-get effect :forall-preconditions))
     (map instantiator (util/safe-get effect :adds))
     (map instantiator (util/safe-get effect :deletes))
     (map #(ground-ncstrips-csp % var-map) (util/safe-get effect :forall-effects))
     (map instantiator (util/safe-get effect :possible-adds))
     (map instantiator (util/safe-get effect :possible-deletes))
     (map #(ground-ncstrips-csp % var-map) (util/safe-get effect :possible-forall-effects))
     (ground-ncstrips-cost (util/safe-get effect :forall-cost) (util/safe-get effect :cost-fn) var-map hla-vars))))


; TODO: put back simplification?  Or provide ground-and-constant-simplify method?
(defn- ground-ncstrips-effect [effect var-map hla-vars]
;  (simplify-ncstrips-effect
   (ground-ncstrips-effect-atoms var-map effect hla-vars))


(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
;	  (filter identity 
     (map #(ground-ncstrips-effect % var-map (:vars schema)) (:effects schema))))

  
; TODO: make more efficient  
;Note that right now, pos-del + add --> add, del + pos-add --> pos-add, del + pos-del --> del.
; Right now, undefined if certain + uncertain effects combined (except delete + pos-add).
; TODO: enforce constraints?  
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
		after-dels    (reduce dissoc clause dels)
 		unks          (concat (filter #(not= :true (after-dels %)) padds)
				      (filter #(= :true (after-dels %))    pdels))]
	   [(into after-dels
	      (concat (map #(vector % :true) adds)
		      (map #(vector % :unknown) unks)))
	     (- ((util/safe-get effect :cost-fn) pred-maps))]))))))

(defn- progress-ncstrips [val desc combiner]
;  (println "proggy " val combiner)
  (let [results 
	(seq 
	 (filter identity
	  (for [clause (:dnf val)
		effect (:effects desc)]
	    (progress-effect-clause effect clause))))]
;    (prn results)
;    (println val desc combiner)
    (if results  
        (dsv/make-dnf-simple-valuation 
          (map first results)
	  (+ (:bound val) (reduce combiner (map second results))))
      (do ;(println "Warning: empty valuation being produced in progress-ncstrips") 
	  *pessimal-valuation*))
))
      
(defmethod progress-optimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc]
  (progress-ncstrips val desc max))

(defmethod progress-pessimistic [:edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation ::NCStripsDescription] [val desc] ;TODO: improve
  (progress-ncstrips val desc min))







)