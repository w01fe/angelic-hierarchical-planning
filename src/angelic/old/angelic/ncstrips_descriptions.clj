(ns angelic.old.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use angelic.old.angelic)
  (:import [java.util ArrayList])
  (:require [angelic.util :as util] 
            [angelic.util.propositions :as props]
            [angelic.old.envs.strips :as strips]
	    [angelic.old.envs.strips.smart-csps :as smart-csps])
  )

;;; NCStrips descriptions

;; Quantification in forall cost effects is assumed to be "max" over rewards, even in pessimistic descriptions!

(derive ::NCStripsDescription :angelic.old.angelic/PropositionalDescription)


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
  (util/assert-is (isa? (:class domain) :angelic.old.envs.strips/StripsPlanningDomain))
  (make-ncstrips-description-schema 
   (util/safe-get domain :types) 
   (props/check-objects (util/safe-get domain :types) (concat (util/safe-get domain :guaranteed-objs) vars)) 
   (util/safe-get domain :predicates)
   (for [clause (next desc)]
     (util/match [#{[:optional [:precondition    ~pre]]
		    [:optional [:effect          ~eff]]
		    [:optional [:possible-effect ~poss]]
		    [:optional [:cost-parameters ~cost-parameters]]
		    [:optional [:cost-precondition ~cost-precondition]]
		    [:cost-expr ~cost-expr]}
		  (partition-all 2 clause)]
       (let [[pos-pre neg-pre forall-pre] (props/parse-pddl-conjunction-forall pre),
	     [add     del     forall-eff] (props/parse-pddl-conjunction-forall eff),
	     [p-add   p-del   forall-p-eff] (props/parse-pddl-conjunction-forall poss),
	     cost-parameters (props/parse-typed-pddl-list cost-parameters)]
;	 (println pos-pre neg-pre forall-pre add del forall-eff p-add p-del forall-p-eff "\n\n")
	 (when cost-precondition (util/assert-is (not (empty? cost-parameters))))
;	 (println cost-expr)
;	 (println (eval '*ns*))
	 (make-ncstrips-effect-schema 
	   pos-pre neg-pre forall-pre 
	   add del forall-eff
	   p-add p-del forall-p-eff 
	   (when cost-parameters [cost-parameters (props/parse-pddl-conjunction cost-precondition) [nil nil]])
	   (binding [*ns* (find-ns 'angelic.old.angelic.ncstrips-descriptions)]
	      (eval `(fn ncstrips-cost-fn ~(vec (map second (concat vars cost-parameters))) ~cost-expr)))))))
   vars))

;   (parse-hierarchy "/Volumes/data/old/Users/jawolfe/projects/angel/src/angelic/old/domains/warehouse.hierarchy" (make-warehouse-strips-domain))


;; At this point, when we instantiate, we have to handle four sets of CSPs
;; For each, we would like to evaluate it now, if possible
;; But this requires that it is both non-const and non-co-referring with other vars - forget it for now
; Deal with everything when we ground it.

; Here, basic task will be to replace preconditions with CSP.
; TODO: Should also maybe constant-simplify preconds at some point, not needed now



(defn instantiate-ncstrips-forall-schema [[args [pos neg] body] vars instance]
  (let [trans-objects (util/safe-get instance :trans-objects)]
  ;   (println "futzing " args pos neg body vars        (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
;       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) args)
;    (print "\nConstructing ncstrips-forall CSP for " args " " vars " "  pos " " neg " " body " : "  )
    [args
     (smart-csps/create-smart-csp pos neg 
       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
       (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) args)
       (:const-pred-map instance) instance)
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
  (util/assert-is (isa? (:class instance) :angelic.old.envs.strips/StripsPlanningInstance))
  (assoc desc :effects (doall (map #(instantiate-ncstrips-effect-schema % (util/safe-get desc :vars) instance) 
				   (util/safe-get desc :effects)))
	 :const-pred-map (get instance :const-pred-map)))


;  (instantiate-hierarchy (parse-hierarchy "/Volumes/data/old/Users/jawolfe/projects/angel/src/angelic/old/domains/warehouse.hierarchy" (make-warehouse-strips-domain)) (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))


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



(comment ; old version without hack for discrete-road-trip
(defn- get-csp-results [csp pos neg var-map pred-maps]
  (let [pl (ArrayList.), nl (ArrayList.)]
    (doseq [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
      (let [final-map (merge var-map combo)  
  	    grounder #(props/simplify-atom final-map %)]
	(doseq [p pos] (.add pl (grounder p)))
	(doseq [n neg] (.add nl (grounder n)))))
    [(seq pl) (seq nl)]))
)

(defn- get-csp-results [csp pos neg var-map pred-maps const-pred-map]
;  (println const-pred-map)
  (let [pl (ArrayList.), nl (ArrayList.)]
    (doseq [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
      (let [final-map (merge var-map combo)  
  	    grounder #(props/simplify-atom final-map %)]
	(doseq [p pos] 
	  (if-let [ca (get const-pred-map (first p))]
	      (when-not (contains? ca (grounder p))
		(.add pl [(gensym)]))
	    (.add pl (grounder p))))
	(doseq [n neg] 
	  (if-let [ca (get const-pred-map (first n))]
	    (when (contains? ca (grounder n))
	      (.add pl [(gensym)]))
	    (.add nl (grounder n)))
	  )))
    [(seq pl) (seq nl)]))

;      [(map grounder pos) (map grounder neg)])))


; We must be careful here!! Old version of forall had a bug ...
;Suppose we have (+/- (P X), - (Q X))
;Execute (forall x (P X) (Q X))
;Correct output: (- (P X), - (Q X)), (+ (P X), + (Q X))
;Current output: (+/- (P X), + (Q X))
;  - misses states, AND adds spurious states 
; Unlike in refinement generation, here we care about possible vs. necessary values.
; Solution: for now, require constant preconditions for foralls -- seems not much of a restriction.


; Make a function that takes pred-maps as arguments and returns grounded [pos neg]
(defn- ground-ncstrips-csp [[args csp [pos neg]] var-map const-pred-map]
  (if (smart-csps/smart-csp-const? csp)
      (let [results (get-csp-results csp pos neg var-map [[:dummy :dummy]] const-pred-map)]
	(fn [pred-maps] results))
 ;   (throw (UnsupportedOperationException. "Forall conditions must be constant."))))
    (fn [pred-maps] (get-csp-results csp pos neg var-map pred-maps const-pred-map))))

(defn- ground-ncstrips-cost [forall cost-fn var-map hla-vars]
  (if (not forall)
      (let [result (apply cost-fn (map #(util/safe-get var-map (second %)) hla-vars))]
	(fn [pred-maps combiner] result))
    (let [early-args (map #(util/safe-get var-map (second %)) hla-vars)
	  [args csp _] forall]
      (fn [pred-maps combiner]
        (reduce combiner  
	  (for [combo (smart-csps/get-smart-csp-solutions csp var-map pred-maps)]
	    (let [final-map (merge combo var-map)]
	      (apply cost-fn (concat early-args (map #(util/safe-get final-map (second %)) args))))))))))
    

(defn- const-simplify-prec [atoms const-pred-map pos?]
  (loop [in (seq atoms) out []]
    (if (nil? in) out
      (if-let [cp (get const-pred-map (ffirst in))]
	  (when (util/same-truth-value? pos? (contains? cp (first in)))
	    (recur (next in) out))
	(recur (next in) (conj out (first in)))))))
	  

; TODO: this is still slow -- set accounts 10% of time! 
; TODO: is this definition of cost-expr sufficiently general?
; TODO: lazy eval cost somehow? (no set)?
(defn- ground-ncstrips-effect-atoms [var-map effect hla-vars const-pred-map]
  (let [instantiator #(props/simplify-atom var-map %)]
    (when-let [pos-pre (const-simplify-prec (map instantiator (util/safe-get effect :pos-preconditions))
					    const-pred-map true)]
      (when-let [neg-pre (const-simplify-prec (map instantiator (util/safe-get effect :neg-preconditions))
					      const-pred-map false)]
	(make-ncstrips-effect 
	 pos-pre
	 neg-pre
     (map #(ground-ncstrips-csp % var-map const-pred-map) (util/safe-get effect :forall-preconditions))
     (map instantiator (util/safe-get effect :adds))
     (map instantiator (util/safe-get effect :deletes))
     (map #(ground-ncstrips-csp % var-map nil) (util/safe-get effect :forall-effects))
     (map instantiator (util/safe-get effect :possible-adds))
     (map instantiator (util/safe-get effect :possible-deletes))
     (map #(ground-ncstrips-csp % var-map nil) (util/safe-get effect :possible-forall-effects))
     (ground-ncstrips-cost (util/safe-get effect :forall-cost) (util/safe-get effect :cost-fn) var-map hla-vars))))))


; TODO: put back simplification?  Or provide ground-and-constant-simplify method?
(defn- ground-ncstrips-effect [effect var-map hla-vars const-pred-map]
;  (simplify-ncstrips-effect
   (ground-ncstrips-effect-atoms var-map effect hla-vars const-pred-map))


(defmethod ground-description ::NCStripsDescriptionSchema [schema var-map]
  (struct ncstrips-description ::NCStripsDescription
   (filter identity 
     (map #(ground-ncstrips-effect % var-map (:vars schema) (util/safe-get schema :const-pred-map)) (:effects schema)))))

  
; TODO: make more efficient  
;Note that right now, pos-del + add --> add, del + pos-add --> pos-add, del + pos-del --> del.
; Right now, undefined if certain + uncertain effects combined (except delete + pos-add).
; TODO: enforce constraints?  


; Current algorithm:
 ; Apply preconditions
 ; Apply deletes
 ; Determine applicable possible-effects
 ; Apply adds 
 ; Apply possible-effects.

; Current matrix:
;    d  a pd pa
;--------------
;d | d  a  d pb
;a |    a  I  I
;pd|      pd pb  
;pa|         pa

; New algorithm:
 ; Apply preconditions
 ; Apply deletes
 ; Apply adds
 ; Apply possible effects
;    d  a pd pa
;--------------
;d | d  a  d pb
;a |    a pb  a
;pd|      pd pb  
;pa|         pa



(defn- progress-effect-clause [effect clause]
;  (println "Progress " effect clause)
  (let [pos-pre (util/safe-get effect :pos-preconditions)
	neg-pre (util/safe-get effect :neg-preconditions)]
    (when (and (every? clause pos-pre)
	       (every? #(not (= :true (clause %))) neg-pre))
      (let [pred-maps (lazy-seq (list (clause->pred-maps clause)))
	    [more-pos-pre more-neg-pre] (apply map concat [nil nil] (map #(% pred-maps) (util/safe-get effect :precondition-fns)))]
;	(println more-pos-pre more-neg-pre)
	(when (and (every? clause more-pos-pre)
		   (every? #(not (= :true (clause %))) more-neg-pre))
	  (let [all-pos-pre   (concat more-pos-pre pos-pre)
		all-neg-pre   (concat more-neg-pre neg-pre)
		after-pre        (into (reduce dissoc clause all-neg-pre) (map #(vector % :true) all-pos-pre))
		[adds dels]   (apply map concat [(util/safe-get effect :adds) (util/safe-get effect :deletes)]
				     (map #(% pred-maps) (util/safe-get effect :effect-fns)))
	       	after-eff     (into (reduce dissoc after-pre dels) (map #(vector % :true) adds))
		[padds pdels] (apply map concat [(util/safe-get effect :possible-adds) (util/safe-get effect :possible-deletes)]
				      (map #(% pred-maps) (util/safe-get effect :possible-effect-fns)))
 		unks          (concat (filter #(nil?    (after-eff %)) padds)
				      (filter #(= :true (after-eff %)) pdels))
		step-rew      (- ((util/safe-get effect :cost-fn) pred-maps max)) ]
	   [(with-meta (into after-eff (map #(vector % :unknown) unks)) 
		       {:src-clause clause :pre-clause after-pre :step-rew step-rew})
	    step-rew]))))))

(defmethod progress-clause ::NCStripsDescription progress-clause-ncstrips [clause desc]
  (util/merge-best > {}
    (for [effect (:effects desc)
	  :let   [result (progress-effect-clause effect clause)
		;  _  (println clause effect result "\n\n\n\n\n\n\n")
		  ]
	  :when result]
	result)))
     
(defmethod regress-clause-state ::NCStripsDescription regress-clause-state-ncstrips [state pre-clause desc post-clause-pair]
  (if-let [[post-clause step-rew] post-clause-pair]
      [(matching-clause-state (util/safe-get (meta post-clause) :pre-clause) state) step-rew]
    (let [candidate-pairs 
	  (for [[post-clause step-rew] (progress-clause pre-clause desc)
		:when (clause-includes-state? post-clause state)]
	    [post-clause step-rew])]
      (when (seq candidate-pairs)
	(let [[post-clause step-rew] (util/first-maximal-element second candidate-pairs)]
	  [(matching-clause-state (util/safe-get (meta post-clause) :pre-clause) state) step-rew pre-clause]))))) 

; You could try to extract the best state going backwards. 
 ; But, you may have a better (i.e., worse) bound than you thought (when there are cost-params).
 ; For now, just return any state and lie about the bound.

;; TODO next: regressing dnf valuations.










;; Want to regress descriptions
 ; Issue: interpretation of foralls is tricky, due to ordering of effects.  (Can't interpret as simple formulae).
 ; Now, foralls are guaranteed to be constant, can forget that they exist. 

; Progression is:

; New algorithm:
 ; Test preconditions
 ; Apply preconditions
 ; Apply deletes
 ; Apply adds
 ; Apply possible effects
;    d  a pd pa
;--------------
;d | d  a  d pb
;a |    a pb  a
;pd|      pd pb  
;pa|         pa

; In regression, if all things were unique, would simply swap effects and preconditions,
; add possible-effects corresponding to negated effects ....

; + x --> pre x, poss-del x
; Poss-add -> Poss-del.

; Preconditions come from effects.
  ; Adds supersede deletes
  ; Then, opposite possibles cancel certains

; Possible effects come from
  ; Negated possible effects
  ; Negated effects 
  ; (just union???)

; Effects are just preconditions  

; How about multiple effects ????????
 ; Would independent be correct?
 ; Even if so, must split since new preconditions may not be disjoint ........
 ; But right now, we don't actually care if preconditions are disjoint .  
  
;; For now, ignore costs.

;; Does not work correctly with foralls with non-const conditions!

(comment ; Seemed to work when last tried, but not in use right now. 
(defmethod invert-description ::NCStripsDescription [desc] 
  (struct ncstrips-description ::NCStripsDescription
   (doall
    (for [effect (util/safe-get desc :effects)]
      (let [pred-maps         :DUMMY
	    [pos-pre neg-pre] (map set 
  	                        (apply map concat [(util/safe-get effect :pos-preconditions)
						 (util/safe-get effect :neg-preconditions)] 
				     (map #(% pred-maps) (util/safe-get effect :precondition-fns))))
	    [adds dels]       (map set
				(apply map concat [(util/safe-get effect :adds) 
						 (util/safe-get effect :deletes)]
				     (map #(% pred-maps) (util/safe-get effect :effect-fns))))
	    [padds pdels]     (map set 
				(apply map concat [(util/safe-get effect :possible-adds) 
						 (util/safe-get effect :possible-deletes)]
				     (map #(% pred-maps) (util/safe-get effect :possible-effect-fns))))]
	(make-ncstrips-effect 
	 (util/difference adds pdels)
	 (util/difference  dels adds padds)
	 nil
	 pos-pre
	 neg-pre
	 nil
	 (util/union dels pdels)
	 (util/union adds padds)
	 nil
	 (fn [pred-maps combiner]
	   (cond (= combiner max) Double/NEGATIVE_INFINITY
		 (= combiner min) Double/POSITIVE_INFINITY
		 :else            (throw (IllegalArgumentException.))))))))))

 )