(ns angelic.domains.unary-cyclic
  (:require [edu.berkeley.ai.util :as util]
            [angelic.sas :as sas]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))


(defn make-unary-cyclic-env []
  (sas/make-sas-problem
   {[:a] (sas/make-sas-var [:a] [[:a -1] [:a 0] [:a 1]])
    [:z] (sas/make-sas-var [:z] [[:z 0] [:z 1]])}
   {[:a] [:a 0]
    [:z] [:z 0]
    sas/goal-var-name sas/goal-false-val}
   [(env-util/make-factored-primitive [:a0-1] {[:a] [:a 0]} {[:a] [:a -1]} -1)
    (env-util/make-factored-primitive [:a-10] {[:a] [:a -1]} {[:a] [:a 0]} -1)
    (env-util/make-factored-primitive [:a01]  {[:a] [:a 0], [:z] [:z 1]} {[:a] [:a 1]} -1)
    (env-util/make-factored-primitive [:z01]  {[:z] [:z 0] [:a] [:a -1]} {[:z] [:z 1]} -1)
    (env-util/make-factored-primitive sas/goal-var-name
                                      {[:a] [:a 1], sas/goal-var-name sas/goal-false-val}
                                      {sas/goal-var-name sas/goal-true-val} 0)]))

;;Var z, vals 0, 1, initially 0.
;;a can transition along the line with no preconditions, except 0-->1 requires z = 1.
;;z can transition 0 --> 1 when a = -1.  

;; Simplest case that breaks ASplan-type planning,
;; Since a must be interleaved with itself. 