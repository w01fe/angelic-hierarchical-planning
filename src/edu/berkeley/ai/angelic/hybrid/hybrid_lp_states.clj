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

(ns edu.berkeley.ai.envs.hybrid-strips.hybrid-lp-states
  (:use clojure.test 
	[edu.berkeley.ai.util :as util]
	[edu.berkeley.ai.util [hybrid :as hybrid] [lp :as lp]]))

(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            Creating lp-state. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct lp-state-struct :state-var-map :incremental-lp)


(defn make-lp-state 
  "Take an assignment from all state variables to numeric values, and make a fresh
   lp-state.  A new variable called [:reward] will be assumed, with val 0, unless provided."
  [initial-state-map]
  )

(defn constrain-lp-state 
  "Apply a hybrid constraint (i.e., precondition).  Return nil for infeasible."
  [state constraint]
  )

(defn split-lp-state 
  "Apply a hybrid constraint (i.e., precondition) and its negation, return [state-if-true, state-if-false].  
   Nil for infeasible."
  [state constraint]
  )

(defn update-lp-state
  "Apply an effect to the state."
  [state constraint]
  )

(defn solve-lp-state
  "Return [var-map rew], where var-map is a mapping from all current state variables and 
   all previous continuous parameters to optimal values, and rew is the corresponding maximal reward."
  [state]
  )


;; TODO: split up hybrid first
;; Then, replicate existing functionality here & verify.
;; Finally, add pass-thru to LP.

;(defn make-lp [bounds objective constraints]
;  {:class ::LP 
;   :constraints constraints
;   :objective   objective
;   :bounds      bounds})


(set! *warn-on-reflection* false)