;; This file provides code to represent (the continuous portions of)
;; planning problem states via LPs.  This includes tracking which LP variable or 
;; constant each state variable refers to at a particular moment, and doing so 
;; in such a way that minimizes the number of LP variables constructed.
;; If called on a concrete hybrid sequence, should never need to make any LP calls. 

(ns edu.berkeley.ai.util.lp-state
  (:use clojure.test 
	[edu.berkeley.ai.util :as util]
	[edu.berkeley.ai.util.hybrid :as hybrid]))

(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            Creating continuous-state   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defn make-lp [bounds objective constraints]
;  {:class ::LP 
;   :constraints constraints
;   :objective   objective
;   :bounds      bounds})


(set! *warn-on-reflection* false)