(ns edu.berkeley.ai.angelic.hierarchies.hybrid-strips-hierarchies
  (:use [edu.berkeley.ai.angelic :as angelic] 
        [edu.berkeley.ai.angelic.hierarchies :as hierarchies])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]]
        [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid]]
        [edu.berkeley.ai.envs.hybrid-strips :as hs]
        [edu.berkeley.ai.angelic.hybrid-ncstrips-descriptions :as hybrid-ncstrips]
        [edu.berkeley.ai.angelic.hybrid-dnf-simple-valuations :as hdsv]
	[edu.berkeley.ai.search.smart-csps :as smart-csps]
        )
  )


;;;; A hybrid version of strips_hierarchies that allows numeric variables and states.

;; For now, hierarchical and refinement preconditions must either be
  ; discrete, or simple range conditions on dummy numeric vars.  
 ; All of the interesting (read difficult) conditions will be handled by ncstrips,
   ; since they may require splits, etc etc.  
 ; I.e., hierarchical preconditions will be simple pos-atoms, neg-atoms, and 
   ; interval constraints on state variables.  
   ; (not really strictly enforced then ???)
   ; constraints on state variables in terms of (!translated!) hierarchical vars?; OK, don't get to prune range of HLA vars, BUT at least correct.



; TODO: MUST enforce that each numeric state variable is used EXACTLY once in each refinement? (????)



;; Refinement schemata

; hla-nv-pos-trans gives [position trans-name] for each var in hla's numeric vars.
(defstruct hybrid-strips-refinement-schema :name  :discrete-vars :numeric-vars :hla-nv-pos-trans :precondition :expansion)
(defn make-hybrid-strips-refinement-schema [name discrete-vars numeric-vars hla-nv-pos-trans precondition expansion]
  (struct hybrid-strips-refinement-schema name  discrete-vars numeric-vars hla-nv-pos-trans precondition expansion))

(def *noop-hs-hla-name* (gensym "noop"))

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


(defn parse-hybrid-strips-refinement-schema [ref discrete-types discrete-vars predicates numeric-types numeric-vars numeric-functions]
  (util/match [[[:optional [:name ~ref-name]]
		[:optional [:parameters ~parameters]]
		[:optional [:precondition ~precondition]]
		[:expansion ~expansion]]
	       (util/partition-all 2 ref)]
    (let [vars (props/parse-typed-pddl-list parameters)
	  [more-discrete-vars more-numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)] 
      (make-hybrid-strips-refinement-schema
       (or ref-name (gensym))
       more-discrete-vars more-numeric-vars
       {} ; Do later
       (hybrid/parse-and-check-constraint precondition 
				   (util/merge-disjoint discrete-vars more-discrete-vars) predicates
				   (util/merge-disjoint numeric-vars more-numeric-vars) numeric-functions true)
       (or (seq expansion) [[*noop-hs-hla-name*]])))))


;; HLA schemata

(defstruct hybrid-strips-hla-schema :class :name :vars :discrete-vars :numeric-vars :split-points :precondition :refinement-schemata :optimistic-schema :pessimistic-schema :primitive)
(defn make-hybrid-strips-hla-schema [name parameters discrete-vars numeric-vars split-points precondition refinement-schemata optimistic-schema pessimistic-schema primitive]
  (struct hybrid-strips-hla-schema ::HybridStripsHLASchema name parameters 
	  discrete-vars numeric-vars split-points precondition
	  refinement-schemata optimistic-schema pessimistic-schema primitive))

(def *noop-hs-hla-schema* 
     (make-hybrid-strips-hla-schema *noop-hs-hla-name* nil nil nil nil hybrid/*true-constraint*
				    nil *identity-description* *identity-description* :noop))


(defn- check-hs-hla-schema [hla-schema all-actions] 
  (util/assert-is (contains? #{nil :noop} (util/safe-get hla-schema :primitive)))
  (util/assert-is (not (map? (:vars hla-schema))))
  (util/assert-is (util/distinct-elts? (map first (:refinement-schemata hla-schema))) "non-distinct refinement names %s" hla-schema)
  (let [var-map (into {} (map (fn [[x y]] [y x]) (:vars hla-schema)))]
    (util/assoc-f hla-schema :refinement-schemata
      (fn [refs] (doall (map #(check-hs-refinement-schema % var-map all-actions) refs))))))


(defn parse-hybrid-strips-hla-schema [hla domain]
;  (println hla)
  (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata]} domain]
   (util/match [#{[:optional [:parameters   ~parameters]]
		 [:optional [:precondition ~precondition]]
		 [:multiple [:refinement   ~refinements]]
		 [:optional [:optimistic   ~optimistic]]
		 [:optional [:pessimistic  ~pessimistic]]
		 [:optional [:exact        ~exact]]}
	       (util/partition-all 2 (next hla))]
    (when exact (util/assert-is (empty? optimistic)) (util/assert-is (empty? pessimistic)))
    (let [name (first hla)
	  vars (props/parse-typed-pddl-list parameters)
	  [discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)] 
      (make-hybrid-strips-hla-schema
       name
       vars discrete-vars numeric-vars
       nil
       (hybrid/parse-and-check-constraint precondition discrete-vars predicates numeric-vars numeric-functions true)
       (doall (map #(parse-hybrid-strips-refinement-schema % discrete-types discrete-vars predicates numeric-types numeric-vars numeric-functions)
		   refinements))
       (parse-description (or optimistic exact [:opt]) domain vars)
       (parse-description (or pessimistic exact [:pess]) domain vars)
       nil)))))



(defn- make-hybrid-strips-primitive-hla-schema [hs-schema discrete-types numeric-types]
  (let [{:keys [name vars split-points precondition effect cost-expr]} hs-schema
	[discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)
	desc (hybrid-ncstrips/make-hybrid-ncstrips-description-schema discrete-vars numeric-vars
	       [(hybrid-ncstrips/make-hybrid-ncstrips-effect-schema precondition effect hybrid/*empty-effect* cost-expr)])]
    (make-hybrid-strips-hla-schema name vars discrete-vars numeric-vars split-points hybrid/*true-constraint* :primitive desc desc hs-schema)))




;; Parse and check an entire hierarchy   

(defn- check-hs-hla-schemata [hla-schemata domain]
  (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata]} domain
	all-actions (util/map-map #(vector (:name %) (map first (:vars %))) (concat hla-schemata (vals action-schemata)))]
 ;   (println (keys all-actions))
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
     (check-hs-hla-schemata (cons *noop-hs-hla-schema* (map #(parse-hybrid-strips-hla-schema % domain) hlas)) domain)}))


(comment
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/road_trip.hierarchy" (make-road-trip-strips-domain))
  (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.hierarchy" (make-hybrid-blocks-strips-domain))
)



;; TODO: flat hybrid strips hierarchy.





;; Planning with hybrid strips hierarchies.

(derive ::HybridStripsHLA               :edu.berkeley.ai.angelic.hierarchies/HLA)
(derive ::HybridStripsPrimitiveHLA      ::HybridStripsHLA)
(derive ::HybridStripsQuasiPrimitiveHLA ::HybridStripsHLA)
(derive ::HybridStripsNoopHLA           ::HybridStripsPrimitiveHLA)

(defstruct hybrid-strips-hla :class :hierarchy :schema :var-map :precondition)

(defn make-hybrid-strips-hla [hierarchy schema var-map precondition primitive]
  (struct hybrid-strips-hla 
	  (cond (= primitive :noop) ::HybridStripsNoopHLA
		(and primitive (not-every? #(util/interval-point (util/safe-get var-map %)) 
					   (keys (util/safe-get schema :numeric-vars))))
                                    ::HybridStripsQuasiPrimitiveHLA
		primitive           ::HybridStripsPrimitiveHLA 
		:else               ::HybridStripsHLA)
	  hierarchy schema var-map precondition))


(defn- extract-preconditions [action-inst hla-map] 
 ; (println "AI" action-inst)
  (let [[act-name & args] action-inst
	hla               (util/safe-get hla-map act-name)
	[pos neg numeric] (util/safe-get hla :precondition)
	trans-var-map     (util/map-map #(vector (second %1) %2) (util/safe-get hla :vars) args)
	simplifier        #(props/simplify-atom trans-var-map %)]
    [(map simplifier pos) (map simplifier neg)]))


(defn- get-hla-nv-pos-trans [numeric-vars expansion hla-map]
  (into {}
    (map (fn [[v t]]
	   (let [app 
		 (for [[i a] (util/indexed expansion) 
		       :let [pos (util/positions v (rest a))]
		       :when (seq pos)]
		   (do (util/assert-is (= (count pos) 1))
		       [i (second (nth (util/safe-get-in hla-map [(first a) :vars]) (first pos)))]))]
	     (util/assert-is (= (count app) 1))
	     [v (first app)]))
	 numeric-vars)))

; Replace precondition with [pos neg numeric], conj on CSP.
(defn instantiate-hybrid-strips-refinement-schema [ref hla-discrete-vars hla-numeric-vars hla-map objects]
  (let [{:keys [discrete-vars precondition expansion]} ref
	all-discrete-vars     (util/merge-disjoint hla-discrete-vars discrete-vars)
	[pos neg numeric]     (hybrid/split-constraint precondition {} objects)
	[first-pos first-neg] (extract-preconditions (first expansion) hla-map)
;	bla (println pos first-pos neg first-neg (util/trans-map hla-discrete-vars objects) (util/trans-map discrete-vars objects))
 	csp (smart-csps/create-smart-csp (set (concat pos first-pos)) (set (concat neg first-neg))
					 (util/trans-map hla-discrete-vars objects)
					 (util/trans-map discrete-vars objects) {})]
    (assoc ref 
      :hla-nv-pos-trans (get-hla-nv-pos-trans hla-numeric-vars expansion hla-map)
      :precondition [pos neg numeric]
      :csp csp)))

; Replace precondition with [pos neg numeric], instantiate descriptions
(defn instantiate-hybrid-strips-hla-schema2 [schema hla-map objects]
;  (println (:name schema))
  (let [discrete-vars (util/safe-get schema :discrete-vars)
	numeric-vars  (util/safe-get schema :numeric-vars)
	refinement-schemata (util/safe-get schema :refinement-schemata)]
    (if (= refinement-schemata :primitive) schema
;    (println refinement-schemata)
     (assoc schema :refinement-schemata 
       (doall (map #(instantiate-hybrid-strips-refinement-schema % discrete-vars numeric-vars hla-map objects) 
  		  refinement-schemata))))))

; Replace precondition with [pos neg numeric], instantiate descriptions
(defn instantiate-hybrid-strips-hla-schema1 [schema instance objects]
  (let [{:keys [precondition optimistic-schema pessimistic-schema]} schema]
    (assoc schema
      :precondition       (hybrid/split-constraint precondition {} objects)
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
			 (make-hybrid-strips-hla-schema root-hla-name [] nil nil nil hybrid/*true-constraint* 
			   [(make-hybrid-strips-refinement-schema 
			     "act" discrete-vars numeric-vars {} hybrid/*true-constraint* [(into '[act] (map second vars))])] 
			   (parse-description [:opt] :dummy :dummy)
			   (parse-description [:pess] :dummy :dummy)
			   nil))
	objects        (util/safe-get instance :objects)
	tmp-hla-map    (util/map-vals #(instantiate-hybrid-strips-hla-schema1 % instance objects) old-hla-map)
	new-hla-map    (util/map-vals #(instantiate-hybrid-strips-hla-schema2 % tmp-hla-map objects) tmp-hla-map)]
    (make-hybrid-strips-hla 
     (struct hybrid-strips-hierarchy ::StripsHierarchy new-hla-map instance)
     (util/safe-get new-hla-map root-hla-name)
     {}
     hdsv/*true-hhp*  ; TODO ???
     false)))


(comment
    (instantiate-hierarchy 
	 (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/road_trip.hierarchy" (make-road-trip-strips-domain)) (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1))

    (instantiate-hierarchy
     (parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.hierarchy" (make-hybrid-blocks-strips-domain))
     (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
     )
)

;; Node methods



(defmethod hla-default-valuation-type ::HybridStripsHLA [hla] 
  :edu.berkeley.ai.angelic.hybrid-dnf-simple-valuations/HybridDNFSimpleValuation)

(defmethod hla-environment ::HybridStripsHLA [hla] (util/safe-get (util/safe-get hla :hierarchy) :problem-instance))

(defmethod hla-name                       ::HybridStripsHLA [hla] 
  (into [(:name (:schema hla))]
	(replace (:var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive? ::HybridStripsHLA [hla] false)
(defmethod hla-primitive ::HybridStripsHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-primitive? ::HybridStripsPrimitiveHLA [hla] true) 
(defmethod hla-primitive ::HybridStripsPrimitiveHLA [hla] 
  (hs/hybrid-strips-action->action (:primitive (:schema hla)) (:var-map hla) (util/safe-get-in hla [:hierarchy :problem-instance :action-space])))

(defmethod hla-primitive? ::HybridStripsNoopHLA [hla] true) 
(defmethod hla-primitive ::HybridStripsNoopHLA [hla] :noop) 


(defmethod hla-hierarchical-preconditions ::HybridStripsHLA [hla]  (:precondition hla))

(defmethod hla-optimistic-description     ::HybridStripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (:var-map hla)))
  
(defmethod hla-pessimistic-description    ::HybridStripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (:var-map hla)))

 

(defmethod hla-immediate-refinements [::HybridStripsPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))


;; TODO: split points -- just bisects for now.
(defmethod hla-immediate-refinements     [::HybridStripsQuasiPrimitiveHLA ::hdsv/HybridDNFSimpleValuation] [hla opt-val]
  (let [{:keys [var-map precondition num-vars]} hla
	var-map (hdsv/restrict-var-map opt-val precondition var-map)
	nv (first num-vars)]
    (util/assert-is (= 1 (count num-vars)))
    (for [i (util/bisect-interval (util/safe-get var-map nv))]
      (assoc hla :var-map (assoc var-map nv i)))))

(defn- translate-var-map "Get the var mappings for hla, given this args and var-map" [hla args var-map]
  (let [hla-vars (:vars hla)]
    (loop [ret {}, args (seq args), vars (seq (:vars hla))]
      (util/assert-is (not (util/xor args vars)))
      (if (not args) ret
	(recur (assoc ret (second (first vars)) (util/safe-get var-map (first args)))
	       (next args) (next vars))))))

(defmethod hla-immediate-refinements     [::HybridStripsHLA ::hdsv/HybridDNFSimpleValuation] [hla opt-val]
  (let [{:keys [var-map num-vars hierarchy precondition]} hla
	hierarchical-precondition                precondition
	opt-val                                  (restrict-valuation opt-val hierarchical-precondition)
	{:keys [hla-map problem-instance]}       hierarchy
	{:keys [domain constant-numeric-vals]}   problem-instance
	{:keys [constant-numeric-functions]}     domain]               
    (when-not (empty-valuation? opt-val)
      (let [val-pred-maps (valuation->pred-maps opt-val)]
	(for [{:keys [discrete-vars numeric-vars hla-nv-pos-trans precondition expansion csp]} (:refinement-schemata (:schema hla))
	      discrete-var-map          (smart-csps/get-smart-csp-solutions csp var-map val-pred-maps)]
	  (let [final-discrete-var-map    (merge var-map discrete-var-map)
		[pos-pre neg-pre num-pre] precondition
		precondition              (hdsv/extract-hybrid-hierarchical-precondition
					   pos-pre neg-pre num-pre final-discrete-var-map
					   constant-numeric-functions constant-numeric-vals)
		new-hierarchical-precondition (hdsv/conjoin-hybrid-hierarchical-preconditions hierarchical-precondition precondition)
		final-var-map           (hdsv/restrict-var-map opt-val new-hierarchical-precondition
					  (util/merge-disjoint final-discrete-var-map 
					    (util/map-vals numeric-vars (constantly util/*real-line*)))) ]
	    (map (fn [call extra-preconditions]
		   (let [hla (util/safe-get hla-map (first call))
			 trans-var-map (translate-var-map hla (next call) final-var-map)
			 [pos-hla neg-hla num-hla] (util/safe-get hla precondition)
			 precondition
			    (hdsv/extract-hybrid-hierarchical-precondition
			     pos-hla neg-hla num-hla trans-var-map constant-numeric-functions constant-numeric-vals)
			 trans-var-map (hdsv/restrict-var-map opt-val precondition trans-var-map)
			 all-preconditions 
  			   (hdsv/conjoin-hybrid-hierarchical-preconditions precondition extra-preconditions)]
		     (make-hybrid-strips-hla hierarchy hla trans-var-map all-preconditions (:primitive hla)))) 
		 expansion
		 (hdsv/split-and-var-translate-hhp new-hierarchical-precondition hla-nv-pos-trans (count expansion)))))))))






#_
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
)





(comment 



;; Grounded STRIPS HLAs and hierarchies (here, actual grounding done JIT, not cached)
; Immediate refinements are [name pos-prec neg-prec CSP (not unk-types) expansion !!!]


	
; This is needed because constant-simplified strips primtitive schemata are in-between full schemata and instances.
(defn- constant-simplify-strips-primitive-schema [primitive const-preds]
  (reduce (fn [m f] (assoc m f (remove #(const-preds (first %)) (util/safe-get m f))))
	  primitive [:pos-pre :neg-pre :add-list :delete-list]))

(defn- get-dummy-var-val-map [objects dummy-var-type-map]
  (util/map-vals (fn [t] (util/safe-get objects t)) dummy-var-type-map))

; CSP takes on sole responsibility for handling *all* constant predicates.  Really (?)
; TODO: drop all constants here!  BUT must do it in right order?
(defn instantiate-strips-hla-schema [schema instance hla-map trans-objects const-pred-map]
  (let [{:keys [name vars pos-pre neg-pre refinement-schemata optimistic-schema pessimistic-schema primitive]} schema
	const-preds  (util/keyset const-pred-map)
	deconst      (fn [atoms] (remove #(const-preds (first %)) atoms))]
 ;   (println name refinement-schemata)
    (make-strips-hla-schema 
     name vars (deconst pos-pre) (deconst neg-pre)
     (or (and (not (coll? refinement-schemata)) refinement-schemata)
      (doall
       (for [[r-name pos-prec neg-prec dummy-type-map expansion] refinement-schemata]   
	 (let [arg-val-map   (util/map-map (fn [[type var]] [var (util/safe-get trans-objects type)]) vars)
	       dummy-val-map (get-dummy-var-val-map trans-objects dummy-type-map)
	       var-map      (into {} (map #(vector % %) (concat (map second vars) (map first dummy-type-map))))
	       [all-pos-pre all-neg-pre]
	          (map concat
		    [pos-prec neg-prec]
                    (extract-preconditions var-map (first expansion) hla-map)
		    (map (fn [precs] (filter #(const-preds (first %)) precs))
		       (apply map concat [nil nil]
			 (map #(extract-preconditions var-map % hla-map)
			      (next expansion)))))]
	   (util/assert-is (not (empty? expansion)))
;	   (print "Constructing CSP for " name " " r-name ": " );(set all-pos-pre) (set all-neg-pre)) 
	   [r-name (deconst pos-prec) (deconst neg-prec) 
	    (smart-csps/create-smart-csp (set all-pos-pre) (set all-neg-pre) arg-val-map dummy-val-map const-pred-map)
	    expansion]))))
     (instantiate-description-schema optimistic-schema instance)
     (instantiate-description-schema pessimistic-schema instance)
     (if (or (not primitive) (= primitive :noop)) primitive  ; TODO: hacky.
	 (constant-simplify-strips-primitive-schema primitive const-preds)))))



(defmethod instantiate-hierarchy ::StripsHierarchySchema [hierarchy instance] 
  (util/assert-is (isa? (:class instance) :edu.berkeley.ai.envs.strips/StripsPlanningInstance))
  (let [old-hla-map    (util/safe-get hierarchy :hlas)
	act-vars       (util/safe-get-in old-hla-map ['act :vars])
	root-hla-name  (gensym "strips-top-level-action")
	old-hla-map    (assoc old-hla-map root-hla-name
			 (make-strips-hla-schema root-hla-name [] nil nil 
			   [["act" nil nil (util/map-map (fn [[t v]] [v t]) act-vars) 
			     [(into '[act] (map second act-vars))]]]
			   (parse-description [:opt] :dummy :dummy)
			   (parse-description [:pess] :dummy :dummy)
			   nil))
	trans-objects  (util/safe-get instance :trans-objects)
	const-pred-map (:const-pred-map instance)
	new-hla-map    (util/map-vals 
			#(instantiate-strips-hla-schema % instance old-hla-map trans-objects const-pred-map)
			old-hla-map)]
    (make-strips-hla 
     (struct strips-hierarchy ::StripsHierarchy new-hla-map instance old-hla-map)
     (util/safe-get new-hla-map root-hla-name)
     {}
     envs/*true-condition*
     false)))    






;; HLA methods
    
(defmethod hla-default-valuation-type ::StripsHLA [hla] 
  :edu.berkeley.ai.angelic.dnf-simple-valuations/DNFSimpleValuation)

(defmethod hla-environment ::StripsHLA [hla] (util/safe-get (util/safe-get hla :hierarchy) :problem-instance))

(defmethod hla-name                       ::StripsHLA [hla] 
  (into [(:name (:schema hla))]
	(replace (:var-map hla) (map second (:vars (:schema hla))))))

(defmethod hla-primitive? ::StripsHLA [hla] false)
(defmethod hla-primitive ::StripsHLA [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-primitive? ::StripsPrimitiveHLA [hla] true) 
(defmethod hla-primitive ::StripsPrimitiveHLA [hla] 
  (strips/strips-action->action (strips/get-strips-action-schema-instance (:primitive (:schema hla)) (:var-map hla))))

(defmethod hla-primitive? ::StripsNoopHLA [hla] true) 
(defmethod hla-primitive ::StripsNoopHLA [hla] :noop) 


(defmethod hla-hierarchical-preconditions ::StripsHLA [hla]  (:precondition hla))

(defmethod hla-optimistic-description     ::StripsHLA [hla]
  (ground-description (:optimistic-schema (:schema hla)) (:var-map hla)))
  
(defmethod hla-pessimistic-description    ::StripsHLA [hla]
  (ground-description (:pessimistic-schema (:schema hla)) (:var-map hla)))

 


(defmethod hla-immediate-refinements [::StripsPrimitiveHLA :edu.berkeley.ai.angelic/Valuation] [hla] (throw (UnsupportedOperationException.)))

(defmethod hla-immediate-refinements     [::StripsHLA :edu.berkeley.ai.angelic/PropositionalValuation] [hla opt-val]
  (let [opt-val      (restrict-valuation opt-val (:precondition hla))
	var-map      (:var-map hla)	
	hierarchy    (:hierarchy hla)
	precondition (:precondition hla)
	hla-map      (:hla-map hierarchy)]
    (when-not (empty-valuation? opt-val)
      (let [val-pred-maps (valuation->pred-maps opt-val)]
  	  (for [[name pos-pre neg-pre csp expansion] (:refinement-schemata (:schema hla))
	        dummy-var-map (smart-csps/get-smart-csp-solutions csp var-map val-pred-maps)]
	    (let [final-var-map (merge var-map dummy-var-map)
		  simplifier #(props/simplify-atom final-var-map %)
		  ground-impl-pre (envs/make-conjunctive-condition
				   (map simplifier pos-pre)
				   (map simplifier neg-pre))]
	      (map (fn [call extra-preconditions]
		     (let [hla (util/safe-get hla-map (first call))
			   trans-var-map (translate-var-map hla (next call) final-var-map)
 	   		   simplifier #(props/simplify-atom trans-var-map %)
			   precond 
			   (envs/conjoin-conditions 
			    (envs/make-conjunctive-condition
			     (map simplifier (util/safe-get hla :pos-pre)) 
			     (map simplifier (util/safe-get hla :neg-pre))) 
			    extra-preconditions)]
		       (make-strips-hla hierarchy hla trans-var-map precond (:primitive hla)))) 
		   expansion
		   (cons (envs/conjoin-conditions precondition ground-impl-pre)
			 (repeat envs/*true-condition*)))))))))


)