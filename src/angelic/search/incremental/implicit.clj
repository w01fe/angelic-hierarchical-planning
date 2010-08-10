(ns angelic.search.incremental.implicit
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is]
            [angelic.search.incremental.hierarchical :as his])
  (:import  [java.util HashMap]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Status ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; status is: :blocked, :solved, or :live
(defn status-val [s]
  (case s
        :blocked -1
        :live    0
        :solved  1))

(defrecord Status [max-reward status])

(def worst-status (Status. is/neg-inf :blocked))
(def best-status  (Status. is/pos-inf :live))

(defn better-status? [s1 s2]
  (or (> (:max-reward s1)
         (:max-reward s2))
      (and (= (:max-reward s1)
              (:max-reward s2))
           (> (status-val (:status s1))
              (status-val (:status s2))))))

(defn- max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

(defn max-status [& stats] (apply max-compare better-status? (cons worst-status stats) ))
(defn min-status [& stats] (apply max-compare (complement better-status?) (cons best-status stats)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def #^HashMap *subproblem-cache* nil)


(defrecord Subproblem [input-set action ^HashMap output-set-cache])

(defrecord OutputSetPointer [subproblem output-set node-atom alt-status])
(defrecord OutputSetNode    [plans plans-status child-pointers])

(declare make-initial-plan)


(defn make-initial-output-set-node [init-set action opt-reward]
  (OutputSetNode.
   (lazy-seq (for [[_ ref] (angelic/immediate-refinements-set)] (make-initial-plan init-set ref)))
   (Status. opt-reward :live)
   nil))


(defn get-subproblem-root-pointer [input-set action]
  (let [context (env/precondition-context action input-set)]
    (util/cache-with *subproblem-cache* [(state/extract-context input-set context) (env/action-name action)]
      (let [logged-input (state/get-logger input-set context)
            subproblem   (Subproblem. logged-input action (HashMap.))
            [opt rew]    (angelic/optimistic-set-and-reward action logged-input)
            init-node    (make-initial-output-set-node logged-input action rew)
            init-pointer (OutputSetPointer. subproblem opt (atom init-node) (Status. rew :blocked))]
        (.put ^HashMap (:output-set-cache subproblem) opt init-pointer)
        init-pointer))))



(defrecord PlanNode [sub-output-set-pointer excluded-children output-set-in-context status])
(defrecord Plan     [plan-nodes status])

;; empty plan?

(defn make-initial-plan [init-set act-seq]
  
  
  )





