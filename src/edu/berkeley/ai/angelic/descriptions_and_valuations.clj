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
  "Does val1 subsume val2, given that they have identical get-valuation-states under subsumption-map?  Return :equal if equal, :strict, or false."
  (fn [val1 val2 subsumption-map] [(:class val1) (:class val2)]))

(defmulti valuation-equals? 
  "Does val1 equal val2, given that they have identical get-valuation-states under subsumption-map?  Return :equal if equal, :strict, or false."
  (fn [val1 val2 subsumption-map] [(:class val1) (:class val2)]))


;;; Methods involving both descriptions and valuations

(defmulti progress-valuation
  "Produce a new valuation representing exactly the result of progressing val through desc."
  (fn [val desc] [(:class val) (:class desc)]))

(defmulti regress-state
  "Take a state, initial valuation, description, and final valuation (presumably but not
   necessarily produced by (progress-valuation preval desc)), where state is consistent with 
   postval, and return a [pre-state rew] with maximal reward where pre-state is consistent
   with preval, and reward is its corresponding reward.  Returns nil if no such state is found."
  (fn [state preval desc postval] [(:class preval) (:class desc) (:class postval)]))



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
  (every? identity (map >= (:reward-seq val1) (:reward-seq val2))))

(defmethod valuation-equals?     [::VectorSubsumptionInfo ::VectorSubsumptionInfo] [val1 val2 subsumption-map]
  (= (:reward-seq val1) (:reward-seq val2)))








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


(defmulti valuation->pred-maps 
  "Compute the a seq of [true poss] maps from pred-name ==> (possibly-)true atom"
  :class)

;;; Descriptions only

(derive ::PropositionalDescription ::Description)

(defmulti parse-description              (fn [desc domain params] (first desc)))

(defmulti instantiate-description-schema (fn [desc instance] (:class desc)))

(defmulti ground-description             (fn [desc var-map] (:class desc)))


;;; Both 

(defmulti progress-clause          
  "Progress this [clause rew] pair through description, returning a new clause->rew map.
   Each result clause should have a :pre-clause metadata, which is the corresponding 
   precondition-restricted version of the initial clause. " 
  (fn [clause desc] (:class desc)))









;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Implementations of trivial valuations and descriptions (explicit, pessimal, optimal, identity, etc.) conditional



;;; Identity descriptions

(derive ::IdentityDescription ::Description)
(def *identity-description* {:class ::IdentityDescription})

(defmethod progress-valuation   [::Valuation ::IdentityDescription] [val desc] val)
(defmethod instantiate-description-schema ::IdentityDescription [desc instance]  desc)
(defmethod ground-description             ::IdentityDescription [desc var-map]  desc)



;;; Explicit valuations and descriptions, 

(derive ::ExplicitValuation ::Valuation)
(defstruct explicit-valuation :class :state-map)

(derive ::PessimalValuation ::ExplicitValuation)
(def *pessimal-valuation* {:class ::PessimalValuation :state-map {}})

(defn- make-explicit-valuation- [state-map]
  (if (empty? state-map) 
      *pessimal-valuation*
    (struct explicit-valuation ::ExplicitValuation state-map)))

(defmethod map->valuation ::ExplicitValuation [type state-map] 
  (make-explicit-valuation- state-map))

(defmethod explicit-valuation-map ::ExplicitValuation [val]
  (:state-map val))

(defmethod restrict-valuation [::ExplicitValuation :edu.berkeley.ai.envs/Condition]
  [val condition]
  (make-explicit-valuation- 
   (reduce (fn [m k] (if (envs/satisfies-condition? k condition) 
		         m
		       (dissoc m k)))
	   (:state-map val) (keys (:state-map val)))))

(defmethod union-valuations [::ExplicitValuation ::ExplicitValuation] [v1 v2]
  (make-explicit-valuation- 
   (util/merge-best > (:state-map v1) (:state-map v2))))



(defstruct explicit-description :class :action-space)
(derive ::ExplicitDescription ::Description)

(defn make-explicit-description [action-space]
  (struct explicit-description ::ExplicitDescription action-space))

(defmethod progress-valuation [::Valuation ::ExplicitDescription]  [val desc]
  (make-explicit-valuation- 
   (util/merge-best > {} 
    (for [[state reward] (explicit-valuation-map val)
	  action (envs/applicable-actions state (:action-space desc))]
      (let [[next step-reward] (envs/next-state-and-reward state action)]
	[next (+ reward step-reward)])))))

(defmethod progress-valuation [::PessimalValuation ::Description]  [val desc] val)

(prefer-method progress-valuation [::Valuation ::IdentityDescription] [::ExplicitValuation ::Description])
(prefer-method progress-valuation [::PessimalValuation ::Description] [::Valuation ::ExplicitDescription])

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
(derive ::ConditionValuation ::Valuation)

(defn make-conditional-valuation 
  [condition max-reward]
  (if (and (envs/consistent-condition? condition) (> max-reward Double/NEGATIVE_INFINITY))
      (struct conditional-valuation ::ConditionalValuation condition max-reward)
    *pessimal-valuation*))

(defn make-optimal-valuation  
  ([] (make-optimal-valuation Double/POSITIVE_INFINITY))
  ([max-reward] (make-conditional-valuation envs/*true-condition* max-reward)))


(defmethod valuation-max-reward ::ConditionalValuation [val] 
  (:max-reward val))

(defmethod restrict-valuation [::ConditionalValuation :edu.berkeley.ai.envs/Condition] 
  [val cond]
  (make-conditional-valuation 
   (envs/conjoin-conditions (:condition val) cond) 
   (:max-reward val)))

(defmethod empty-valuation? ::ConditionalValuation [val] false)

(defmethod get-valuation-states ::ConditionalValuation [val subsumption-map] [(gensym) nil])


; TODO: union here?  Regress?


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


(defmethod parse-description :opt [desc domain params]
  (util/assert-is (<= (count desc) 2))
  (if (= (count desc) 1)
      (make-optimal-description)
    (make-optimal-description (second desc))))

(defmethod instantiate-description-schema ::ConditionalDescription [desc instance] desc)

(defmethod ground-description ::ConditionalDescription [desc var-map]
  (make-conditional-description 
   (envs/ground-propositional-condition (util/safe-get desc :condition) var-map)
   (util/safe-get desc :max-reward)))

























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

(def *no-subsumption-info* {:class ::NoSubsumptionInfo})
(defmethod valuation-subsumes?     [::NoSubsumptionInfo ::NoSubsumptionInfo] [val1 val2 subsumption-map] true)



(defmulti invert-description (fn [desc] (:class desc)))

(defmulti regress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti regress-pessimistic (fn [val desc] [(:class val) (:class desc)]))

(defmethod regress-optimistic :default [val desc]
  (progress-optimistic val (invert-description desc)))

(defmethod regress-pessimistic :default [val desc]
  (progress-pessimistic val (invert-description desc)))
)