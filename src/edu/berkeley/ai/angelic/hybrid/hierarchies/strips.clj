(ns edu.berkeley.ai.angelic.hybrid.hierarchies.strips
  (:use edu.berkeley.ai.angelic 
        edu.berkeley.ai.angelic.hierarchies
        edu.berkeley.ai.angelic.hybrid )
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
        [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid] 
	 [intervals :as iv] [linear-expressions :as le]]
	[edu.berkeley.ai.envs.strips.smart-csps :as smart-csps]
        [edu.berkeley.ai.envs.hybrid-strips :as hs]
	[edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
        [edu.berkeley.ai.angelic.hybrid.ncstrips-descriptions :as hybrid-ncstrips]
        [edu.berkeley.ai.angelic.hybrid.dnf-lp-valuations :as hdlv]
        )
  )


;;;; A hybrid version of strips_hierarchies that allows numeric variables and states.

;; The only restriction imposed is that the conditions for forall clauses in 
;; hierarchical and refinement preconditions must be fully known when an HLA is created.
;; (this could be relaxed a bit).  In other words, they must involve only constant
;; propositions/variables, or at least be guaranteed to hold one way or another
;; based on the optimistic description.  

;; TODO: be careful about mapping numeric varaibles, so that if they appear multiple times
;; in a refinement they end up mapping to the same LP variables.

;; TODO: provide a mechanism to ground variables in advance based on optimal high-level solutions (?)
;; i.e., just add this to hierarchical preconditions. 

;; TODO: add constant simplification.

;; Have to be careful of variable collisions in numeric vars in hierarchical preconditions, if we try
;; to wait til the end to translate.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           Parsing hierarchy schemata
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct hybrid-strips-refinement-schema :name  :discrete-vars :numeric-vars :precondition :expansion)
(defn make-hybrid-strips-refinement-schema [name discrete-vars numeric-vars precondition expansion]
  (struct hybrid-strips-refinement-schema name  discrete-vars numeric-vars precondition expansion))

(def *noop-hs-hla-name*   (gensym "noop"))
(def *finish-hs-hla-name* (gensym "finish"))

(defn- check-hs-refinement-schema [ref hla-var-map all-actions]
  (let [{:keys [discrete-vars numeric-vars expansion]} ref
	all-vars (reduce util/merge-disjoint hla-var-map [discrete-vars numeric-vars])]
    (assoc ref :expansion
      (doall 
       (for [action expansion]
	 (let [params (next action)
	       declared-types (util/safe-get all-actions (first action))]
	   (util/assert-is (= (count params) (count declared-types)))
	   (util/assert-is (every? identity (map #(= %1 (util/safe-get all-vars %2)) declared-types params)))
	   (vec action)))))))


(defn parse-hybrid-strips-refinement-schema [ref discrete-types discrete-vars predicates numeric-types numeric-vars numeric-functions const-numeric-functions]
  (util/match [[[:optional [:name ~ref-name]]
		[:optional [:parameters ~parameters]]
		[:optional [:precondition ~precondition]]
		[:expansion ~expansion]]
	       (partition-all 2 ref)]
    (let [vars (props/parse-typed-pddl-list parameters)
	  [more-discrete-vars more-numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)] 
      (make-hybrid-strips-refinement-schema
       (or ref-name (gensym))
       more-discrete-vars more-numeric-vars
       (hc/parse-and-check-constraint precondition 
	  (util/merge-disjoint discrete-vars more-discrete-vars) predicates
          (util/merge-disjoint numeric-vars more-numeric-vars) numeric-functions 
          const-numeric-functions)
       (or (seq expansion) [[*noop-hs-hla-name*]])))))


;; HLA schemata

(defstruct hybrid-strips-hla-schema :class :name :vars :discrete-vars :numeric-vars :split-points :precondition :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)
(defn make-hybrid-strips-hla-schema [name parameters discrete-vars numeric-vars split-points precondition refinement-schemata optimistic-schema pessimistic-schema primitive]
  (struct hybrid-strips-hla-schema ::HybridStripsHLASchema name parameters 
	  discrete-vars numeric-vars split-points precondition
	  refinement-schemata optimistic-schema pessimistic-schema primitive))

(def *noop-hs-hla-schema* 
     (make-hybrid-strips-hla-schema *noop-hs-hla-name* nil nil nil nil hc/*true-constraint*
				    nil *identity-description* *identity-description* :noop))
(def *finish-hs-hla-schema* 
     (make-hybrid-strips-hla-schema *finish-hs-hla-name* nil nil nil nil hc/*true-constraint*
				    nil *hybrid-finish-description-schema* *hybrid-finish-description-schema* :noop))


(defn- check-hs-hla-schema [hla-schema all-actions] 
  (util/assert-is (contains? #{nil :noop} (util/safe-get hla-schema :primitive)))
  (util/assert-is (not (map? (:vars hla-schema))))
  (util/assert-is (util/distinct-elts? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
  (let [var-map (into {} (map (fn [[x y]] [y x]) (:vars hla-schema)))]
    (util/assoc-f hla-schema :refinement-schemata
      (fn [refs] (doall (map #(check-hs-refinement-schema % var-map all-actions) refs))))))


(defn parse-hybrid-strips-hla-schema [hla domain]
;  (println hla)
  (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata constant-numeric-functions]} domain]
   (util/match [#{[:optional [:parameters   ~parameters]]
		 [:optional [:precondition ~precondition]]
		 [:multiple [:refinement   ~refinements]]
		 [:optional [:optimistic   ~optimistic]]
		 [:optional [:pessimistic  ~pessimistic]]
		 [:optional [:exact        ~exact]]}
	       (partition-all 2 (next hla))]
    (when exact (util/assert-is (empty? optimistic)) (util/assert-is (empty? pessimistic)))
    (let [name (first hla)
	  vars (props/parse-typed-pddl-list parameters)
	  [discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)] 
      (make-hybrid-strips-hla-schema
       name
       vars discrete-vars numeric-vars
       nil
       (hc/parse-and-check-constraint precondition 
         discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions)
       (doall (map #(parse-hybrid-strips-refinement-schema % discrete-types discrete-vars predicates 
                      numeric-types numeric-vars numeric-functions constant-numeric-functions)
		   refinements))
       (parse-description (or optimistic exact [:opt]) domain vars)
       (parse-description (or pessimistic exact [:pess]) domain vars)
       nil)))))


(defn- make-hybrid-strips-primitive-hla-schema [hs-schema discrete-types numeric-types]
  (let [{:keys [name vars split-points precondition effect cost-expr]} hs-schema
	[discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)
	desc (hybrid-ncstrips/make-hybrid-ncstrips-description-schema discrete-vars numeric-vars
	       [(hybrid-ncstrips/make-hybrid-ncstrips-effect-schema precondition effect he/*empty-effect* cost-expr)])]
    (make-hybrid-strips-hla-schema name vars discrete-vars numeric-vars split-points hc/*true-constraint* :primitive desc desc hs-schema)))




;; Parse and check an entire hierarchy   

(defn- check-hs-hla-schemata [hla-schemata domain]
  (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata]} domain
	all-actions (util/map-map #(vector (:name %) (map first (:vars %))) (concat hla-schemata (vals action-schemata)))]
    (util/assert-is (= (count all-actions) (+ (count action-schemata) (count hla-schemata))))
    (let [hla-schemata (doall (map #(check-hs-hla-schema % all-actions) hla-schemata))]
      (util/assert-is (some #(= (:name %) 'act) hla-schemata))
      (util/map-map #(vector (:name %) %) 
	(concat hla-schemata
	  (map #(make-hybrid-strips-primitive-hla-schema % discrete-types numeric-types)
	       (vals action-schemata)))))))

     
(defmethod parse-hierarchy-type :hybrid-strips-hierarchy [type contents domain]
  (util/assert-is (isa? (:class domain) ::hs/HybridStripsPlanningDomain))
  (util/match [[[:multiple (:hla ~@hlas)]] contents]
    {:class ::HybridStripsHierarchySchema, :hlas
     (check-hs-hla-schemata (concat [*noop-hs-hla-schema* *finish-hs-hla-schema*] 
                                    (map #(parse-hybrid-strips-hla-schema % domain) hlas)) domain)}))



(comment
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/road_trip.hierarchy" (make-road-trip-strips-domain))
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/simple_road_trip.hierarchy" (make-simple-road-trip-strips-domain))
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.hierarchy" (make-hybrid-blocks-strips-domain))
)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           Instantiating hierarchy schemata
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::HybridStripsHLA               :edu.berkeley.ai.angelic.hierarchies/HLA)
(derive ::HybridStripsQuasiPrimitiveHLA ::HybridStripsHLA)
(derive ::HybridStripsNoopHLA           ::HybridStripsQuasiPrimitiveHLA)

(defstruct hybrid-strips-hla :class :hierarchy :schema :disc-var-map :cont-var-map :precondition)

(defn make-hybrid-strips-hla [hierarchy schema disc-var-map cont-var-map precondition primitive]
  (struct hybrid-strips-hla 
	  (cond (= primitive :noop) ::HybridStripsNoopHLA
                primitive           ::HybridStripsQuasiPrimitiveHLA
		:else               ::HybridStripsHLA)
	  hierarchy schema disc-var-map cont-var-map precondition))


(defn- extract-preconditions [action-inst hla-map] 
 ; (println "AI" action-inst)
  (let [[act-name & args] action-inst
	hla               (util/safe-get hla-map act-name)
	[pos neg numeric] (util/safe-get hla :split-precondition)
	trans-var-map     (util/map-map #(vector (second %1) %2) (util/safe-get hla :vars) args)
	simplifier        #(props/simplify-atom trans-var-map %)]
    [(map simplifier pos) (map simplifier neg)]))


; Replace precondition with [pos neg numeric], conj on CSP.
(defn instantiate-hybrid-strips-refinement-schema [ref hla-discrete-vars hla-numeric-vars hla-map instance]
;  (println ref)
  (let [objects (util/safe-get instance :objects)
        {:keys [discrete-vars precondition expansion]} ref
	all-discrete-vars     (util/merge-disjoint hla-discrete-vars discrete-vars)
	[pos neg numeric]     (hc/split-constraint precondition {} objects)
	[first-pos first-neg] (extract-preconditions (first expansion) hla-map)
 	csp (smart-csps/create-smart-csp (set (concat pos first-pos)) (set (concat neg first-neg))
					 (util/trans-map hla-discrete-vars objects)
					 (util/trans-map discrete-vars objects) {} instance)]
    (assoc ref :csp csp)))

; Instantiate refinement schemata
(defn instantiate-hybrid-strips-hla-schema2 [schema hla-map instance]
  (let [discrete-vars (util/safe-get schema :discrete-vars)
	numeric-vars  (util/safe-get schema :numeric-vars)
	refinement-schemata (util/safe-get schema :refinement-schemata)]
    (if (= refinement-schemata :primitive) schema
     (assoc schema :refinement-schemata 
       (doall (map #(instantiate-hybrid-strips-refinement-schema % discrete-vars numeric-vars hla-map instance) 
  		  refinement-schemata))))))

; Instantiate HLA preconditions and description schemata
(defn instantiate-hybrid-strips-hla-schema1 [schema instance]
  (let [{:keys [precondition optimistic-schema pessimistic-schema]} schema]
    (assoc schema
      :split-precondition       (hc/split-constraint precondition {} (util/safe-get instance :objects))
      :optimistic-schema  (instantiate-description-schema optimistic-schema instance)
      :pessimistic-schema (instantiate-description-schema optimistic-schema instance))))

; Can split-constraint with empty var map, construct smart CSPs here. 
; In instantiation, run CSP, then get numeric yield, then ...

(defstruct hybrid-strips-hierarchy :class :hla-map :problem-instance)

(defmethod instantiate-hierarchy ::HybridStripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) ::hs/HybridStripsPlanningInstance))
  (let [old-hla-map    (util/safe-get hierarchy :hlas)
	act-schema     (util/safe-get old-hla-map 'act)
	{:keys [vars discrete-vars numeric-vars]} act-schema
	root-hla-name  (gensym "hybrid-strips-top-level-action")
	old-hla-map    (assoc old-hla-map root-hla-name
			 (make-hybrid-strips-hla-schema root-hla-name [] nil nil nil hc/*true-constraint* 
			   [(make-hybrid-strips-refinement-schema 
			     "act" discrete-vars numeric-vars hc/*true-constraint* [(into '[act] (map second vars))])] 
			   (parse-description [:opt] :dummy :dummy)
			   (parse-description [:pess] :dummy :dummy)
			   nil))
	tmp-hla-map    (util/map-vals #(instantiate-hybrid-strips-hla-schema1 % instance) old-hla-map)
        new-hla-map    (util/map-vals #(instantiate-hybrid-strips-hla-schema2 % tmp-hla-map instance) tmp-hla-map)
        hierarchy      (struct hybrid-strips-hierarchy ::StripsHierarchy new-hla-map instance)]
    [(make-hybrid-strips-hla hierarchy (util/safe-get new-hla-map root-hla-name) {} {} hdlv/*true-scc* false)
     (make-hybrid-strips-hla hierarchy (util/safe-get new-hla-map *finish-hs-hla-name*) {} {} hdlv/*true-scc* :noop)]))


(comment
    (instantiate-hierarchy 
	 (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/road_trip.hierarchy" (make-road-trip-strips-domain)) (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1))

    (instantiate-hierarchy
     (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.hierarchy" (make-hybrid-blocks-strips-domain))
     (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
     )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           Planning (Node methods)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn get-full-var-map [hla]
  (util/merge-disjoint (util/safe-get hla :disc-var-map) (util/safe-get hla :cont-var-map)))

(defmethod hla-default-optimistic-valuation-type ::HybridStripsHLA [hla]  
  ::hdlv/HybridDNFLPValuation)
(defmethod hla-default-pessimistic-valuation-type ::HybridStripsHLA [hla]  
  ::hdlv/HybridDNFLPValuation)

(defmethod hla-environment ::HybridStripsHLA [hla] 
  (util/safe-get (util/safe-get hla :hierarchy) :problem-instance))

(defmethod hla-name                       ::HybridStripsHLA [hla] 
  (into [(:name (:schema hla))]
	(replace (get-full-var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive? ::HybridStripsHLA [hla] false)
(defmethod hla-primitive ::HybridStripsHLA [hla] (throw (UnsupportedOperationException.)))

(defstruct hybrid-strips-hla :class :hierarchy :schema :disc-var-map :cont-var-map :precondition)

(defmethod hla-primitive? ::HybridStripsQuasiPrimitiveHLA [hla] true) 
(defmethod hla-primitive ::HybridStripsQuasiPrimitiveHLA [hla]
  (let [{:keys [schema disc-var-map cont-var-map]} hla
        prim-schema (util/safe-get schema :primitive)
        {:keys [precondition effect cost-expr]} prim-schema
        [p n num] (hc/split-constraint precondition disc-var-map (util/safe-get-in hla [:hierarchy :problem-instance :objects]))]   
    (assoc 
        (struct hs/hybrid-strips-quasi-action prim-schema disc-var-map (set p) (set n) (keys cont-var-map) num)
      :num-var-map cont-var-map)))


(defmethod hla-primitive? ::HybridStripsNoopHLA [hla] true) 
(defmethod hla-primitive ::HybridStripsNoopHLA [hla] :noop) 


(defmethod hla-hierarchical-preconditions ::HybridStripsHLA [hla]  (:precondition hla))

(defmethod hla-optimistic-description     ::HybridStripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (get-full-var-map hla)))
  
(defmethod hla-pessimistic-description    ::HybridStripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (get-full-var-map hla)))

 

(defmethod hla-immediate-refinements [::HybridStripsPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))



;; TODO: use vars, numeric-vars, discrete-vars fields to simultaneously translate both var maps. 
(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map]
  (let [hla-vars (:vars hla)]
    (loop [ret {}, args (seq args), vars (seq (:vars hla))]
      (util/assert-is (not (util/xor args vars)))
      (if (not args) ret
	(recur (assoc ret (second (first vars)) (util/safe-get var-map (first args)))
	       (next args) (next vars))))))


(defmethod hla-immediate-refinements     [::HybridStripsHLA ::hdlv/HybridDNFLPValuation] [hla opt-val]
  (let [{:keys [disc-var-map cont-var-map hierarchy]} hla
        hierarchical-scc                         (util/safe-get hla :precondition)
	opt-val                                  (restrict-valuation opt-val hierarchical-scc)
	{:keys [hla-map problem-instance]}       hierarchy
	{:keys [objects constant-numeric-vals]}  problem-instance]               
    (assert (and objects constant-numeric-vals))
    (when-not (empty-valuation? opt-val)
      (let [val-pred-maps (valuation->pred-maps opt-val)]
	(for [{:keys [discrete-vars numeric-vars precondition expansion csp]} (:refinement-schemata (:schema hla))
	      ref-disc-var-map          (smart-csps/get-smart-csp-solutions csp disc-var-map val-pred-maps)]
	  (let [final-disc-var-map        (util/merge-disjoint disc-var-map ref-disc-var-map)
                ref-cont-var-map          (util/map-map (fn [[k v]] [k (gensym (str k))]) numeric-vars)
                final-cont-var-map        (util/merge-disjoint cont-var-map ref-cont-var-map)
                refinement-scc            (envs/conjoin-conditions 
                                           (:precondition hla)
                                           (hdlv/constraint->simple-constraint-condition 
                                            precondition final-disc-var-map final-cont-var-map objects constant-numeric-vals))]
            (for [[call first?] (map vector expansion (cons true (repeat false)))]
              (let [ref-hla            (util/safe-get hla-map (first call))
                    [trans-disc-var-map trans-cont-var-map]
                                       (reduce (fn [[tdv tcv] [tv val]]
                                                 (util/cond-let [tval]
                                                   (final-disc-var-map val) 
                                                     [(assoc tdv tv tval) tcv]
                                                   (final-cont-var-map val)
                                                     [tdv (assoc tcv tv tval)]
                                                   :else (throw (RuntimeException. (str "Unbound var " tv)))))
                                               [{} {}]
                                               (map #(vector (second %1) %2) (:vars ref-hla) (next call)))
                    ref-hla-scc        (hdlv/constraint->simple-constraint-condition 
                                        (util/safe-get ref-hla :precondition) 
                                        trans-disc-var-map trans-cont-var-map objects constant-numeric-vals)
                    final-scc          (if first? (envs/conjoin-conditions refinement-scc ref-hla-scc) ref-hla-scc)]
                (make-hybrid-strips-hla hierarchy ref-hla trans-disc-var-map trans-cont-var-map 
                                        final-scc (:primitive ref-hla))))))))))




(comment
    (instantiate-hierarchy 
	 (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/road_trip.hierarchy" (make-road-trip-strips-domain)) (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1))

    (interactive-search  (alt-node (instantiate-hierarchy
                                    (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.hierarchy" (make-hybrid-blocks-strips-domain))
                                    (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
                                    ) {:cache? false :graph? false}))
    
    
 (let [e (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])]
    (map :name (extract-hybrid-primitive-solution e 
                 (first (interactive-search (alt-node (get-hierarchy *hybrid-blocks-hierarchy* e)
                                                 {:cache? false :graph? false :ref-choice-fn first-choice-fn}))))))
)




(comment 





; - Issue with split points:
;  - Numeric fn vals become intervals
;  - Split points become intervals
;  - Numeric fn vals become intervals on expressions
;  - ........
;  - (or, regions become polytopes, set of constraints, rather than set
;     of intervals. )
;   - With ordinary bisection, ... 
;      - this does not really come up except with pessimistic descriptions?
;  
; Think: progress situation where block A, width 2, has center [1,
;  3] on B of width 4.  Put down C (width 1) on block B.  
;
;Split DNf into two clauses:
;
;Both: A on B, C on B.
;1: A left of C:    A in [1,2], C in [A+1.5, 3.5]
;2. A right of C: A in [2, 3], C in [A-1.5, 3.5]
;
;Or, if you like, A in [1,2], C in [2.5, 3.5], A + 1.5 < C.
;
;Now, put down D (with .5) on block B .......
;Still get set of binary inequalities, in fact, always
;of form 0 <= A - 1 <= C - 2.5 <= d - 3.25 <= .5 
;
;These can always be checked for feasibility in constant time.
;
;Moreover, reward can be sum of expressions ...
;  but must refer to block positions at particular points in time.
;  i.e., must maintain constraints as well.
;
;Final output of plan will essentially be set of LPs ? (equivalent to
;ILP, more or less -- better or worse?).  
;
;(for single plan, entire problem is not ILP -- PSPACE...)

;Hmmm.

;This may even happen when split points are not intervals? ?? 
;Then, things may be even harder (assuming split points capture all
;discrete behavior.).

;Lets say we try to do with pure split points. 

;A on B, center in [1, 3].
;Put down C on B, width 1.  
;Initial interval: [.5, 3.5].  Get optimistic cost, no pessimistic?
;Split to [.5 2], [2 3.5].  Get Optimistic, pessimistic must deal with
;overlap.  Can store constraint C + 1.5 < B, OR choose arbitrary split:
;C in [.5, 1], B in [1.3] (i.e.).  Ideally, would depend on future?

;Reward here must be a single number.  (?).  Or, we're back in ILP land
;(?).


; TODO: check on testing feasibility of linear program 
;  - same as solving system of equations in constraints-vars unknowns?  n^2.5-3?

; TODO: think about complextiy of hybrid-blocks. 
;  - Hypothesis:
;    - LP (poly) iff all fully feasible intervals for putdown specified
          ; (X left of Y)  n^4.5.
;    - NP complete otherwise (rational block sizes).


;; Old version - based on bisecting intervals rather than LPs.
;(defmethod hla-immediate-refinements     [::HybridStripsQuasiPrimitiveHLA ::hdsv/HybridDNFSimpleValuation] [hla opt-val]
;  (let [{:keys [var-map precondition num-vars]} hla
;	var-map (hdsv/restrict-var-map opt-val precondition var-map)
;	nv (first num-vars)]
 ;   (util/assert-is (= 1 (count num-vars)))
;    (for [i (iv/bisect-interval (util/safe-get var-map nv))]
;      (assoc hla :var-map (assoc var-map nv i)))))
)

