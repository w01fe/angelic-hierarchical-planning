;; This file defines valuations for hybrid problems, where the discrete part of the state
;; is always known but we may be angelic about the continuous part.  

;; In particular, a hybrid-fixed-lp-valuation consists of a set of true discrete propositions,
;; together with a continuous-lp-state for the continuous variables.  

(ns edu.berkeley.ai.angelic.hybrid.hybrid-fixed-lp-valuations
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