;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: states.clj
;;
;;  Representations and simple functions for factored states and set thereof.

(ns angel.search.states.binary
 (:refer-clojure)
 (:use angel.search.states angel.util)
 )

(derive ::BinaryStateSet ::angel.search.states/StateSet)
(derive ::BinaryStateSpace ::angel.search.states/StateSpace)
;(derive ::BinaryStateSpace ::BinaryStateSet)

;(defstruct binary-state-set :class :space :formula)

(defstruct binary-list-state :class :space :true-vars)

(defn make-binary-list-state [space true-vars]
  (dorun #(assert (contains? (:var-map space) %)) true-vars) 
  (struct binary-list-state ::BinaryListState space true-vars))

(defstruct binary-state-space :class :var-array :var-map)

(defn make-binary-state-space [vars] 
  "Make a binary state space from a set of variables"
  (struct binary-state-space ::BinaryStateSpace (to-array vars) (zipmap vars (nats))))

(defmethod list-states ::BinaryStateSpace [state-set]
  (:states state-set))

(defmethod canonicalize ::BinaryStateSpace [state-set]
  state-set)

(defmethod set-contains? ::BinaryStateSpace [state-set elt] 
  (contains? (:states state-set) elt))


(comment 
;; Class hierarchy

(derive ::BooleanStateSpace ::StateSpace)

(defn make-boolean-state-space [vars] 
  {:class ::BooleanStateSpace :vars vars})




(defn make-boolean-state [space val-map] 
  (assoc val-map :class ::BooleanState :state-space space))




;(defn make-state-set 

(defmulti enumerate-states :class)

(declare enumerate-boolean-maps)

(defn enumerate-boolean-maps [vars]
  (if (nil? vars)
    [{}]
    (let [recs (enumerate-boolean-maps (rest vars))]
      (for [item '(true false) state recs] 
        (assoc state (first vars) item)))))

(defmethod enumerate-states ::BooleanStateSpace [space]
  (map #(make-state space %) (enumerate-boolean-maps (:vars space))))

)