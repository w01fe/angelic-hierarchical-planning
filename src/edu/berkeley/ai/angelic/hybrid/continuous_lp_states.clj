;; This file provides code to represent (the continuous portions of)
;; planning problem states via LPs.  This includes tracking which LP variable or 
;; constant each state variable refers to at a particular moment, and doing so 
;; in such a way that minimizes the number of LP variables constructed.
;; If called on a concrete hybrid sequence, should never need to make any LP calls. 

;; Have to deal with two kinds of variables: grounded numeric state variables,
;; and dummy numeric parameters for an HLA (always unique).
;; Numeric parameters don't change, and always correspond to LP vars directly.
;; If they are grounded, we should already get a number, so we have to deal with those too (maybe)?

;; By default, returned states are guaranteed to be feasible.

(ns edu.berkeley.ai.angelic.hybrid.continuous-lp-states
  (:use clojure.test 
	[edu.berkeley.ai.util :as util]
	[edu.berkeley.ai.util [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]))

(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            Creating lp-state. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(derive ::ContinuousLPState ::le/ContinuousState)
(defstruct lp-state-struct :state-var-map :incremental-lp :reward-const)
(util/deftype ::ContinuousLPState make-lp-state*
  (fn [state-var-map incremental-lp reward-const] 
    (struct lp-state-struct state-var-map incremental-lp reward-const))
  (fn [lps] (vals lps)))

(def get-state-var-map (accessor lp-state-struct :state-var-map))
(def get-incremental-lp (accessor lp-state-struct :incremental-lp))
(def get-reward-const (accessor lp-state-struct :reward-const))

; LP variables are verbatim HLA parameters, and should be unique symbols or keywords.  
; State variables should be vectors.  We will make explicit use of this here ...

; State-var-map is a map from state variables to maps from LP variables (incl. *one-var*) 
; to multipliers.  


;; TODO: extract bounds from LP, use to simplify things, ...

;; TODO: figure out smart way to handle forall conditions.  For instance,
;; when moving left in hybrid-blocks, we only need to consider rightmost obstructing block.

;; TODO: what do we do about strict inequalities?  For now, disallow them ?

;; For simplicity, we have one fake LP variable representing constant value of one.
; For now, assume we're always given things in nice "map" linear form.

;; TODO TODO TODO: Using nil as one will interfere with bounds, etc. ... need to bite the bullet and
;; have bona fide constant terms. 
 ; - but only for LP.  lp-state can stick with nil.  
 ; - in fact, linear-expressions should probably just move to this format too.  



(defn make-lp-state 
  "Take a concrete assignment from all state variables to numeric values, and make a fresh
   (immutable) lp-state.  nil acts like a special lp parameter, set to unity."
  ([initial-state-map] (make-lp-state initial-state-map 0))
  ([initial-state-map initial-reward]
;  (assert (every? vector? (keys initial-state-map)))
   (make-lp-state* 
    (map-vals #(hash-map nil %) initial-state-map)
    (lp/make-incremental-lp {} {} {})
    initial-reward)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Updating
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn add-lp-state-param 
  "Add a new parameter to the LP, with optional bounds.  If no bounds give, param will start unbounded."
  ([state param] (add-lp-state-param state param [nil nil]))
  ([state param bounds]
     (assert (not (get (get-state-var-map state) param)))
     (assoc state :incremental-lp (add-lp-var (get-incremental-lp state) param bounds))))



(defn- constrain-lp-state [state constraint]
  (println constraint)
  (cond (true? constraint) state
	(false? constraint) nil
	:else (when-let [new-lp (add-lp-constraint (get-incremental-lp state) constraint)]
		(assoc state :incremental-lp new-lp))))
				       

(defn constrain-lp-state-gez 
  "Constrain constraint-lm linear-map to evaluate >= 0.  Return nil for inconsistent."
  [state constraint-lm]
  (constrain-lp-state state (le/linear-expr-gez->normalized-inequality 
			     (le/map-linear-expr-vars (get-state-var-map state) constraint-lm))))


(defn constrain-lp-state-lez 
  "Constrain constraint-lm linear-map to evaluate <= 0.  Return nil for inconsistent."
  [state constraint-lm]
  (constrain-lp-state state (le/linear-expr-lez->normalized-inequality
			     (le/map-linear-expr-vars (get-state-var-map state) constraint-lm))))

(defn constrain-lp-state-eqz 
  "Constrain constraint-lm linear-map to evaluate = 0.  Return nil for inconsistent."
  [state constraint-lm]
  (constrain-lp-state state (le/linear-expr-eqz->normalized-inequality
			     (le/map-linear-expr-vars (get-state-var-map state) constraint-lm))))
  
	    

(defn update-lp-state
  "Effects is a map from state variables to maps specifying their new values as linear combinations
    of old state variables and parameters.  
   Reward is another linear combination term that will be added to the reward."  
  [state effects reward]
  (let [old-state-var-map (get-state-var-map state)
	lp                (get-incremental-lp state)
	reward            (map-linear-expr-vars old-state-var-map reward)]
    (make-lp-state* 
     (persistent!
      (reduce (fn [new-state-var-map [effect-var effect-lm]]
		(assert (contains? old-state-var-map effect-var))
		(assoc! new-state-var-map effect-var 
			(map-linear-expr-vars old-state-var-map effect-lm)))
	      (transient old-state-var-map) effects))
     (increment-lp-objective lp (dissoc reward nil))
     (+ (get-reward-const state) (get reward nil 0)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Solving
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn solve-lp-state
  "Return [cont-state var-map rew], where cont-state maps state variables to values (a ContinuousMapState),
   var-map is a mapping from continuous parameters to to optimal values, and rew is the corresponding 
   maximal reward."
  [state]
  (let [[var-map rew] (lp/solve-incremental-lp (get-incremental-lp state))]
    [(map-vals (fn [lm] (le/evaluate-linear-expr var-map lm))
	       (get-state-var-map state))
     var-map
     (+ rew (get-reward-const state))]))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest continuous-lp-states 
  ;Simple example, test bounds etc.
  (is (= (-> (make-lp-state {[:a] 1}) 
	     (add-lp-state-param :c [0 2]) 
	     (update-lp-state nil {:c 5 nil 2 [:a] 1}) 
	     (solve-lp-state))
	 [{[:a] 1} {:c 2} 13]))

  ; Slightly more complex example; simulate a single "right" action
  ; that can increment position between 0 and 5, followed by a constraint
  ; that we get to state 3.
  (is (= (-> (make-lp-state {[:pos] 1}) 
	     (add-lp-state-param :right)
	     (constrain-lp-state-gez {:right 1})
	     (constrain-lp-state-lez {:right 1 nil -5})
	     (update-lp-state {[:pos] {:right 1 [:pos] 1}} {:right 1 nil 10})
	     (constrain-lp-state-eqz {[:pos] 1 nil -3})
	     (solve-lp-state)
	     )
	 [{[:pos] 3} {:right 2} 12]))

  ; More complex example; simulate a "right1" action
  ; that uses less of a resource but costs more, followed by 
  ; a "right2" action that uses more resource but is cheaper.
  ; Thus, we have to optimize resource use vs. cost.
  (is (= (-> (make-lp-state {[:pos] 0 [:resource] 15}) 

	     (add-lp-state-param :right1)
	     (constrain-lp-state-gez {:right1 1})
	     (constrain-lp-state-lez {:right1 1 nil -10})
	     (update-lp-state {[:pos] {:right1 1 [:pos] 1}
			       [:resource] {[:resource] 1 :right1 -1}}
			      {:right1 -2 nil -10})

	     (add-lp-state-param :right2)
	     (constrain-lp-state-gez {:right2 1})
	     (constrain-lp-state-lez {:right2 1 nil -10})
	     (update-lp-state {[:pos] {:right2 1 [:pos] 1}
			       [:resource] {[:resource] 1 :right2 -2}}
			      {:right2 -1 nil -10})

	     (constrain-lp-state-eqz {[:pos] 1 nil -10})
	     (constrain-lp-state-gez {[:resource] 1})
	     (solve-lp-state)
	     )
	 [{[:pos] 10 [:resource] 0} {:right1 5 :right2 5} -35]))

  )



(set! *warn-on-reflection* false)