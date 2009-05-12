(in-ns 'edu.berkeley.ai.angelic)

;;;; Valuations represent a mapping from states to reward (e.g., value functions).
; Descriptions are transition functions on valuations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Ordinary valuations and descriptions

;;; Methods on just valuations

; core methods

(defmulti map->valuation 
  "Get a valuation of type representing these mappings."
  (fn [type state] type))

(defmulti explicit-valuation-map
  "Get an explicit map from states to values."
  :class)

(defmulti restrict-valuation 
  "Restrict this valuation to states satisfying condition (an ::envs/Condition)"
  (fn [val condition] [(:class val) (:class condition)]))

(defmulti union-valuations
  "Get a valuation representing the state-wise max of val1 and val2"
  (fn [val1 val2] [(:class val1) (:class val2)]))

; derived methods

(defmulti empty-valuation? 
  "Does this valuation have no states reachable with reward > -inf?"
  :class)

(defmulti valuation-state-reward 
  "Get the reward val associates with this state"
  (fn [val state] (:class val)))

(defmulti valuation-max-reward-state
  "Get a best [state rew] pair consistent with this valuation, or nil if none"
  :class)

(defmulti valuation-max-reward
  "Get the max-reward assigned to any reachable state, or -inf if none"
  :class)

; subsumption methods

(def *subsumption-preds-gt* 
     [(fn [al1 al2] (>= (apply max al1) (apply max al2)))
      (fn [al1 al2] (= (apply max al1) (apply max al2)))])

(def *subsumption-preds-lt* 
     [(fn [al1 al2] (<= (apply min al1) (apply min al2)))
      (fn [al1 al2] (= (apply min al1) (apply min al2)))])

(def *subsumption-preds-ignore* 
     [(fn [al1 al2] true)
      (fn [al1 al2] true)])
  

(defmulti get-valuation-states 
  "Get a (hopefully canonical), possibly implicit representation of the state set, 
   ignoring predicates in subsumption-map, plus an auxillary representation of this 
   remaining information that should be passed to valuation-subsumes.
   subsumption-map maps predicate names to [>=-fn =-fn], which act on seqs of tuples 
   of pred args."
  (fn [val subsumption-map] (:class val)))

(defmulti valuation-subsumes? 
  "Does val1 subsume val2, given that they have identical get-valuation-states under subsumption-map?  Return :strict if every state is assigned > value, :equal if equal, :weak if every state is >= and at least some state is equal (incl. equal), or false/nil."
  (fn [val1 val2 subsumption-map] [(:class val1) (:class val2)]))


;;; Methods involving both descriptions and valuations


(defmulti progress-valuation
  "Produce a new valuation representing exactly the result of progressing val through desc."
  (fn [val desc] [(:class val) (:class desc)]))

(defmulti regress-state
  "Take a state, initial valuation, description, and final valuation (presumably but not
   necessarily produced by (progress-valuation preval desc)), where state is consistent with 
   postval, and return a [pre-state step-rew pre-rew optional-pre-clause] with maximal reward where pre-state is consistent
   with preval, and step-rew is its corresponding step reward.  Returns nil if no such state is found."
  (fn [state-rew preval desc postval] [(:class preval) (:class desc) (:class postval)]))



;; Some default method implementations

(defn state->valuation [type state] 
  (map->valuation type {state 0}))

(defmethod valuation-max-reward-state :default [v]
  (when-let [m (seq (explicit-valuation-map v))] (util/first-maximal-element val m)))

(defmethod valuation-max-reward       :default [v]
  (if-let [[state val] (valuation-max-reward-state v)]
      val
    Double/NEGATIVE_INFINITY))

(defmethod empty-valuation? :default [val] 
  (= (valuation-max-reward val) Double/NEGATIVE_INFINITY))

(defmethod valuation-state-reward :default [val state] 
  (get (explicit-valuation-map val) state Double/NEGATIVE_INFINITY))


(defmethod get-valuation-states ::Valuation [v subsumption-map]
  (util/assert-is (empty? subsumption-map))
  (let [ordered-pairs (sort-by #(hash (key %)) (explicit-valuation-map v))]
    [(map key ordered-pairs)
     {:class ::VectorSubsumptionInfo :reward-seq (map val ordered-pairs)}]))

(defmethod valuation-subsumes?     [::VectorSubsumptionInfo ::VectorSubsumptionInfo] [val1 val2 subsumption-map]
  (cond (every? identity (map > (:reward-seq val1) (:reward-seq val2)))  :strict
	(= (:reward-seq val1) (:reward-seq val2))                        :equal
	(every? identity (map >= (:reward-seq val1) (:reward-seq val2))) :weak))









;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Propositional valuations and descriptions

;;; Conjunctive clauses are represented as maps from atoms to :true or :unknown (false is implicit).

;;; Valuations

(derive ::PropositionalValuation ::Valuation)

(import '[java.util HashMap])

(defn clause->pred-maps [conjunctive-clause]
  (let [true-map (HashMap.) poss-map (HashMap.)]
    (doseq [[#^clojure.lang.APersistentVector pred stat] conjunctive-clause]
      (let [#^HashMap m (if (= stat :true) true-map poss-map)
	    pred-name (.get pred 0)]
	(.put m pred-name (cons pred (.get m pred-name)))))
    [true-map poss-map]))

(defn clause-includes-state? [clause state]
  (and (every? #(contains? clause %) state)
       (every? (fn [[atom tv]] (not (and (= tv :true) (not (contains? state atom))))) clause)))

(defn minimal-clause-state [clause]
  (set (map key (filter (fn [p] (= (val p) :true)) clause))))

(defn matching-clause-state [clause state]
;  (util/assert-is (clause-includes-state? clause state)) ;; TODO: remove!!
  (let [[true-atoms unk-atoms] (util/separate (fn [p] (= (val p) :true)) clause)]
    (set (concat (map key true-atoms)
		 (filter state (map key unk-atoms))))))

(defn state->clause [state]
 (util/map-map #(vector % :true) state))

(defn clause-subsumes? [c1 c2]
  (and (every? (fn [[atom tv]] 
		 (if (= tv :true) 
		     (= (get c2 atom) :true)
		   true))
	       c1)
       (every? (fn [[atom tv]]
		 (if (= tv :true)
		     (contains? c1 atom)
		   (= (get c1 atom) :unknown)))
	       c2)))


(defmulti valuation->pred-maps 
  "Compute the a seq of [true poss] maps from pred-name ==> (possibly-)true atom"
  :class)

(defmulti valuation-clause-map 
  "Return a mapping from conjunctive clauses to rewards."
  :class)

(defmulti filter-valuation-clauses 
  "Like filter, but on [clause rew] pairs."
  (fn [f v] (:class v)))

(defmulti map-valuation-rewards
  "Transform valuation rewards with a unary function."
  (fn [f v] (:class v)))

(defmulti valuation-max-reward-clause
  "Get [clause rew], where clause has the max reward."
  :class)

(defmulti valuation-clause-reward
  "Get the [clause rew] pair for clause, or return nil."
  (fn [v c] (:class v)))

(defmulti valuation-state-clause-reward
  "Get the best [clause rew] pair for state, or return nil."
  (fn [v s] (:class v)))

(defmulti add-clause-metadata 
  "Add the provided mappings to metadata of all clauses in this valuation."
  (fn [v m] (:class v)))

(defmethod add-clause-metadata :default [v m] v)

(defmethod filter-valuation-clauses :default [f v] v)

(defn restrict-clause [clause condition]
  (util/assert-is (isa? (:class condition) :edu.berkeley.ai.envs/ConjunctiveCondition))
  (let [pos (envs/get-positive-conjuncts condition)
	neg (envs/get-negative-conjuncts condition)]
    (when-let [after-pos
	       (loop [pos pos clause clause]
		 (cond (empty? pos)                   clause
		       (contains? clause (first pos)) (recur (next pos) (assoc clause (first pos) :true))
		       :else nil))]
      (loop [neg neg clause after-pos]
	(cond (empty? neg)                       clause
	      (= :true (get clause (first neg))) nil
	      :else  (recur (next neg) (dissoc clause (first neg))))))))

;;; Descriptions only

(derive ::PropositionalDescription ::Description)

(defmulti parse-description              (fn [desc domain params] (first desc)))

(defmulti instantiate-description-schema (fn [desc instance] (:class desc)))

(defmulti ground-description             (fn [desc var-map] (:class desc)))


;;; Both 

(defmulti progress-clause          
  "Progress this clause pair through description, returning a new clause->rew map.  Implementers may choose to add metadata to resulting clauses, to 
improve efficiency of regression."
  (fn [clause desc] (:class desc)))

(defmulti regress-clause-state          
  "rerogress this state through desc, returning a [state step-rew optional-pre-clause] pair.
   post-clause-rew is optional, but may speed things up; if provided, it must 
   be a [clause rew] resulting from progress-clause on pre-clause desc, and must
   have state as a model." 
  (fn [state pre-clause desc post-clause-rew] (:class desc)))


(defmulti regress-state-hinted
  "Take a state, initial valuation, description, and final valuation (presumably but not
   necessarily produced by (progress-valuation preval desc)), and optional final clause, where state is consistent with 
   postval and clause, and return a [pre-state step-rew pre-rew optional-pre-clause] with maximal reward where pre-state is consistent
   with preval, and step-rew is its corresponding step reward.  Returns nil if no such state is found."
  (fn [state preval desc postval clause] [(:class preval) (:class desc) (:class postval)]))

(defmethod regress-state-hinted :default regress-state-hinted-default [state pre-val desc post-val clause]
  (when-let [[pre-state step-rew] (regress-state state pre-val desc post-val)]
    [pre-state step-rew (valuation-state-reward pre-val pre-state) nil]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Implementations of trivial valuations and descriptions (explicit, pessimal, optimal, identity, etc.) conditional



;;; Identity descriptions

(derive ::IdentityDescription ::Description)
(def *identity-description* {:class ::IdentityDescription})

(defmethod progress-valuation   [::Valuation ::IdentityDescription] [val desc] val)
(defmethod instantiate-description-schema ::IdentityDescription [desc instance]  desc)
(defmethod ground-description             ::IdentityDescription [desc var-map]  desc)
(defmethod regress-state   [::Valuation ::IdentityDescription ::Valuation] [state pre-val desc post-val]
  [state 0])
(defmethod regress-state-hinted [::Valuation ::IdentityDescription ::Valuation] regress-state-hinted-identity [state pre-val desc post-val clause]
  (if-let [[pre-clause pre-rew] (valuation-clause-reward pre-val clause)]
      [state 0 pre-rew pre-clause]
    [state 0 (valuation-state-reward pre-val state)]))

(defmethod progress-clause       ::IdentityDescription [clause desc]
  {clause 0})
(defmethod regress-clause-state  ::IdentityDescription [state pre-clause desc post-clause-rew]
  [state 0])

;;; Finish description

(derive ::FinishDescription ::PropositionalDescription)
(def *finish-description* {:class ::FinishDescription})
(def *finish-state*  #{[(gensym "goal")]})
(def *finish-clause* (state->clause *finish-state*))
(defmethod instantiate-description-schema ::FinishDescription [desc instance]  
  (assoc desc :goal (envs/get-goal instance)))
(defmethod ground-description             ::FinishDescription [desc var-map]  desc)

(defmethod progress-valuation    [::ConditionalValuation ::FinishDescription] [val desc]
  (if (envs/consistent-condition? (envs/conjoin-conditions (util/safe-get val :condition)
						      (util/safe-get desc :goal)))
    (map->valuation ::ExplicitValuation {*finish-state* (valuation-max-reward val)})))


(defmethod regress-state    [::ConditionalValuation ::FinishDescription ::Valuation] [state preval desc postval]
  (let [condition (util/safe-get preval :condition)
	goal      (util/safe-get desc :goal)]
    [(util/to-set (envs/get-positive-conjuncts (envs/conjoin-conditions condition goal))) 0]))

(defmethod regress-state    [::ExplicitValuation ::FinishDescription ::Valuation] [state preval desc postval]
  (if-let [s (util/find-first #(envs/satisfies-condition? % (util/safe-get desc :goal)) 
			 (keys (explicit-valuation-map val)))]
    [s 0]))


(defmethod progress-clause       ::FinishDescription [clause desc]
  (when-let [restricted (restrict-clause clause (util/safe-get desc :goal))]
    {*finish-clause* 0}))

(defmethod regress-clause-state  ::FinishDescription [state pre-clause desc post-clause-rew]
  (util/assert-is (= state *finish-state*))
  (when-let [restricted (restrict-clause pre-clause (util/safe-get desc :goal))]
    [(minimal-clause-state restricted) 0]))



;;; Explicit valuations and descriptions, 

(derive ::ExplicitValuation ::Valuation)
(defstruct explicit-valuation :class :state-map)

(derive ::PessimalValuation ::ExplicitValuation)
(def *pessimal-valuation* {:class ::PessimalValuation :state-map {}})

(defn make-explicit-valuation [state-map]
  (if (empty? state-map) 
      *pessimal-valuation*
    (struct explicit-valuation ::ExplicitValuation state-map)))

(defmethod map->valuation ::ExplicitValuation [type state-map] 
  (make-explicit-valuation state-map))

(defmethod explicit-valuation-map ::ExplicitValuation [val]
  (:state-map val))

(defmethod restrict-valuation [::ExplicitValuation :edu.berkeley.ai.envs/Condition]
  [val condition]
  (make-explicit-valuation 
   (reduce (fn [m k] (if (envs/satisfies-condition? k condition) 
		         m
		       (dissoc m k)))
	   (:state-map val) (keys (:state-map val)))))

(defmethod union-valuations [::ExplicitValuation ::ExplicitValuation] [v1 v2]
  (make-explicit-valuation 
   (util/merge-best > (:state-map v1) (:state-map v2))))

(defmethod union-valuations [::PessimalValuation ::Valuation] [v1 v2] v2)
(defmethod union-valuations [::Valuation ::PessimalValuation] [v1 v2] v1)
(defmethod union-valuations [::PessimalValuation ::PessimalValuation] [v1 v2] v1)

(defmethod valuation-clause-map ::PessimalValuation [val]
  {})

(defmethod valuation-clause-reward ::PessimalValuation [val c]
  nil)


(defstruct explicit-description :class :action-space)
(derive ::ExplicitDescription ::Description)

(defn make-explicit-description [action-space]
  (struct explicit-description ::ExplicitDescription action-space))

(defmethod progress-valuation [::Valuation ::ExplicitDescription]  [val desc]
  (make-explicit-valuation 
   (util/merge-best > {} 
    (for [[state reward] (explicit-valuation-map val)
	  action (envs/applicable-actions state (:action-space desc))]
      (let [[next step-reward] (envs/next-state-and-reward state action)]
	[next (+ reward step-reward)])))))

(defmethod progress-valuation [::PessimalValuation ::Description]  [val desc] val)

(defmethod progress-valuation    [::ExplicitValuation ::FinishDescription] progress-explicit-final [val desc]
  (if (some #(envs/satisfies-condition? % (util/safe-get desc :goal)) (keys (explicit-valuation-map val)))
    (map->valuation ::ExplicitValuation {*finish-state* (valuation-max-reward val)})
    *pessimal-valuation*))

(prefer-method progress-valuation [::PessimalValuation ::Description] [::ExplicitValuation ::FinishDescription])


(defmethod regress-state [::Valuation ::PessimalDescription ::Valuation] [state pre-val desc post-val]
  nil)

(defmethod regress-state [::PessimalValuation ::Description ::Valuation] [state pre-val desc post-val]
  nil)

(defmethod regress-state [::PessimalValuation ::PessimalDescription ::Valuation] [state pre-val desc post-val]
  nil)

(defmethod regress-clause-state ::PessimalDescription [state pre-clause desc post-clause-rew] nil)

(prefer-method progress-valuation [::Valuation ::IdentityDescription] [::ExplicitValuation ::Description])
(prefer-method progress-valuation [::PessimalValuation ::Description] [::Valuation ::ExplicitDescription])
(prefer-method progress-valuation [::PessimalValuation ::Description] [::Valuation ::IdentityDescription])

;;; Pessimal valuations and descriptions


(derive ::PessimalDescription ::Description)
(def *pessimal-description* {:class ::PessimalDescription})

(defmethod progress-valuation   [::Valuation ::PessimalDescription] [val desc]  *pessimal-valuation*)
(defmethod parse-description :pess [desc domain params] (util/assert-is (= (count desc) 1)) *pessimal-description*)
(defmethod instantiate-description-schema ::PessimalDescription [desc instance] desc)
(defmethod ground-description ::PessimalDescription [desc var-map] desc)

(prefer-method progress-valuation [::PessimalValuation ::Description] [::Valuation ::PessimalDescription])

  




;;; Conditional and optimal valuations and descriptions

(defstruct conditional-valuation :class :condition :max-reward)
(derive ::ConditionalValuation ::Valuation)

(defn make-conditional-valuation 
  [condition max-reward]
  (if (and (envs/consistent-condition? condition) (> max-reward Double/NEGATIVE_INFINITY))
      (struct conditional-valuation ::ConditionalValuation condition max-reward)
    *pessimal-valuation*))

(defn make-optimal-valuation  
  ([] (make-optimal-valuation Double/POSITIVE_INFINITY))
  ([max-reward] (make-conditional-valuation envs/*true-condition* max-reward)))


(defmethod valuation-state-reward ::ConditionalValuation [v state]
  (if (envs/satisfies-condition? state (:condition v))
      (:max-reward v)
    Double/NEGATIVE_INFINITY))

(defmethod valuation-max-reward ::ConditionalValuation [val] 
  (:max-reward val))

(defmethod valuation-max-reward-state ::ConditionalValuation [val] 
  [(util/to-set (envs/get-positive-conjuncts (:condition val)))
   (:max-reward val)])

(defmethod restrict-valuation [::ConditionalValuation :edu.berkeley.ai.envs/Condition] 
  [val cond]
  (make-conditional-valuation 
   (envs/conjoin-conditions (:condition val) cond) 
   (:max-reward val)))

(defmethod empty-valuation? ::ConditionalValuation [val] false)

(defmethod get-valuation-states ::ConditionalValuation [val subsumption-map] [(gensym) nil])


; Union valuation

(derive ::UnionValuation ::Valuation)
(defmethod union-valuations [::Valuation ::Valuation] [v1 v2]
  {:class ::UnionValuation :components [v1 v2]})

(defmethod union-valuations [::UnionValuation ::Valuation] [v1 v2]
  {:class ::UnionValuation :components (cons v2 (:components v1))})

(defmethod union-valuations [::Valuation ::UnionValuation] [v1 v2]
  {:class ::UnionValuation :components (cons v1 (:components v2))})

(prefer-method union-valuations [::PessimalValuation ::Valuation] [::Valuation ::UnionValuation])
(prefer-method union-valuations [::Valuation ::PessimalValuation] [::UnionValuation ::Valuation])

(defmethod union-valuations [::UnionValuation ::UnionValuation] [v1 v2]
  {:class ::UnionValuation :components (concat (:components v2) (:components v1))})

(defmethod valuation-state-reward ::UnionValuation valuation-state-reward-union [v state]
  (reduce max (map #(valuation-state-reward % state) (:components v))))

(defmethod valuation-max-reward ::UnionValuation valuation-max-reward-union [v]
  (reduce max (map valuation-max-reward (:components v))))

(defmethod valuation-max-reward-state ::UnionValuation valuation-max-reward-state-union [v]
  (util/first-maximal-element second (map valuation-max-reward-state (:components v))))

(defmethod restrict-valuation [::UnionValuation :edu.berkeley.ai.envs/Condition] restrict-valuation-union [v c]
  (let [comps (remove #(identical? % *pessimal-valuation*) 
		      (map #(restrict-valuation % c) (:components v)))]
    (cond (empty? comps) *pessimal-valuation*
	  (util/singleton? comps) (first comps)
	  :else (assoc v :components comps))))

(defmethod empty-valuation? ::UnionValuation [v] (every? empty-valuation? (:components v)))

; Conditional description

(defstruct conditional-description :class :condition :max-reward)
(derive ::ConditionalDescription ::Description)

(defn make-conditional-description [condition max-reward]
  (if (or (= condition envs/*false-condition*)
	  (= max-reward Double/NEGATIVE_INFINITY))
      *pessimal-description*
    (struct conditional-description ::ConditionalDescription condition max-reward)))

(defn make-optimal-description
  ([] (make-optimal-description Double/POSITIVE_INFINITY))
  ([opt-rew] (make-conditional-description envs/*true-condition* opt-rew)))


(defmethod progress-valuation [::Valuation ::ConditionalDescription] [val desc]
  (make-conditional-valuation 
   (:condition desc) 
   (+ (:max-reward desc)
      (valuation-max-reward val))))

(defmethod progress-clause  ::ConditionalDescription [clause desc]
  {(util/safe-get desc :condition-dnf) 
   (util/safe-get desc :max-reward)})

(defmethod regress-state [::Valuation ::ConditionalDescription ::Valuation] [state pre-val desc post-val]
  [(first (valuation-max-reward-state pre-val))
   (:max-reward desc)])

(defmethod regress-state-hinted [::Valuation ::ConditionalDescription ::Valuation] regress-state-hinted-conditional [state pre-val desc post-val clause]
  (if (isa? (:class pre-val) ::PropositionalValuation)
      (when-let [[pre-clause pre-rew] (valuation-max-reward-clause pre-val)]
	[(minimal-clause-state pre-clause) (:max-reward desc) pre-rew pre-clause])
    (when-let [[pre-state pre-rew] (valuation-max-reward-state pre-val)]
      [pre-state (:max-reward desc) pre-rew])))

(defmethod regress-clause-state ::ConditionalDescription [state pre-clause desc post-clause-rew] 
  [(minimal-clause-state pre-clause) (:max-reward desc)])

(defmethod parse-description :opt [desc domain params]
  (util/assert-is (<= (count desc) 2))
  (if (= (count desc) 1)
      (make-optimal-description)
    (make-optimal-description (second desc))))

(defmethod instantiate-description-schema ::ConditionalDescription [desc instance] 
;  (println "inst!")
  (let [condition (:condition desc)
	pos       (envs/get-positive-conjuncts condition)
	neg       (envs/get-negative-conjuncts condition)]
    (assoc desc
      :condition-dnf 
        (into 
	 (apply dissoc 
		(util/map-map #(vector % :unknown) (util/safe-get instance :all-atoms))
		neg)
	 (map #(vector % :true) pos)))))

(defmethod ground-description ::ConditionalDescription [desc var-map]
  (assoc desc 
    :condition (envs/ground-propositional-condition (util/safe-get desc :condition) var-map)))

























(comment ; deprecated 

(defmulti get-valuation-lower-bound 
  "Get the min-reward assigned to any reachable state, or -inf if none"
  :class)

(defmulti intersect-valuations 
  "Intersect these valuations, keeping the reward part from the first."
  (fn [v1 v2] [(:class v1) (:class v2)]))

(defmulti sub-intersect-valuations 
  "Like intersect-valuations, but returns a non-empty subset of the intersection as quickly as possible."
  (fn [v1 v2] [(:class v1) (:class v2)]))



(defmulti invert-description (fn [desc] (:class desc)))

(defmulti regress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti regress-pessimistic (fn [val desc] [(:class val) (:class desc)]))

(defmethod regress-optimistic :default [val desc]
  (progress-optimistic val (invert-description desc)))

(defmethod regress-pessimistic :default [val desc]
  (progress-pessimistic val (invert-description desc)))
)