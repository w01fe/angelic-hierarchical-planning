(ns angelic.domains.hanoi
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

(defn make-hanoi-env [n-disks n-pegs]
  (assert (= n-pegs 3))
  (sas/make-sas-problem
   (into {sas/goal-var-name sas/goal-var}
         (for [i (range n-disks)]
           [[:disk i] (sas/make-sas-var [:disk i] (set (range n-pegs)))]))
   (into {sas/goal-var-name sas/goal-false-val}
         (for [i (range n-disks)]
           [[:disk i] 0]))
   (cons
    (env-util/make-factored-primitive
     [:goal]
     (into {sas/goal-var-name sas/goal-false-val}
           (for [disk (range n-disks)]
             [[:disk disk] 2]))     
     {sas/goal-var-name sas/goal-true-val}
     0)
    
    (for [disk (range n-disks)
          from (range n-pegs)
          to   (disj #{0 1 2} from)]
      (env-util/make-factored-primitive
       [disk from to]
       (into {[:disk disk] from}
             (for [smaller (range (inc disk) n-disks)]
               [[:disk smaller] (util/safe-singleton (disj #{0 1 2} from to))]))
       {[:disk disk] to}
       -1)))))



;;Var z, vals 0, 1, initially 0.
;;a can transition along the line with no preconditions, except 0-->1 requires z = 1.
;;z can transition 0 --> 1 when a = -1.  

;; Simplest case that breaks ASplan-type planning,
;; Since a must be interleaved with itself.


