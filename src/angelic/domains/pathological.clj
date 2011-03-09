(ns angelic.domains.pathological
  (:require [angelic.util :as util]
            [angelic.sas :as sas]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simplest demonstration of how asplan-type bounded intention planning fails in cyclic causal
;; graphs, even if all actions are unary.
(defn make-unary-cyclic-env []
  (sas/make-sas-problem
   {sas/goal-var-name sas/goal-var
    [:a] (sas/make-sas-var [:a] [[:a -1] [:a 0] [:a 1]])
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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple demonstration of how previous asplan implementation failed,
;; by doing the top-down thing incorrectly
;; (failing to account for if current val needed.)

;;   A
;; B   C
;; D / |
;; E   F
;;   G

;; E should use C's value first, B should use A's value first, D wants to make first transition
;; with B's init val, E wants D's value 

(defn make-top-down-env []
  (let [var-names #{:a :b :c :d :e :f}]
   (sas/make-sas-problem
    (into {sas/goal-var-name sas/goal-var}
          (for [n (disj var-names :e)]
            [n (sas/make-sas-var n #{0 1 2})]))
    (into {sas/goal-var-name sas/goal-false-val}
          (for [n var-names]
            [n 0]))
    [(env-util/make-factored-primitive [:a01] {:a 0} {:a 1} -1)
     (env-util/make-factored-primitive [:a01] {:a 1} {:a 2} -1)     
     (env-util/make-factored-primitive [:b01] {:a 0, :b 0} {:b 1} -1)     
     (env-util/make-factored-primitive [:c01] {:a 1, :c 0} {:c 1} -1)
     (env-util/make-factored-primitive [:c12] {:a 2, :c 1} {:c 2} -1)          
     (env-util/make-factored-primitive [:d01] {:b 0, :d 0} {:d 1} -1)
     (env-util/make-factored-primitive [:d12] {:b 1, :d 1} {:d 2} -1)
     (env-util/make-factored-primitive [:e01] {:c 2, :e 0} {:e 1} -1)
     (env-util/make-factored-primitive [:e12] {:d 2, :e 1} {:e 2} -1)
     (env-util/make-factored-primitive [:f01] {:c 1, :f 0} {:f 1} -1)                    
     (env-util/make-factored-primitive sas/goal-var-name
                                       {:e 2, :f 1 sas/goal-var-name sas/goal-false-val}
                                       {sas/goal-var-name sas/goal-true-val} 0)])))