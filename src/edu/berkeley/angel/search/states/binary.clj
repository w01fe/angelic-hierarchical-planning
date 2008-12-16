;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: states.clj
;;
;;  Representations and simple functions for factored states and set thereof.

(ns angel.search.states.binary
 (:refer-clojure)
 (:use angel.search.states angel.util )
 )


;; Binary states

;(derufe ::BinaryState ::FactoredState)
(derive ::BinaryListState ::BinaryState)
(derive ::BinarySetState ::BinaryState)


(defstruct binary-vector-state :class :space :true-vars)

(defn make-binary-vector-state [space true-vars]
  (doseq [x true-vars]  #(assert-is (member? x (:vars space))))
  (assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-vector-state ::BinaryListState space (apply vector true-vars)))


(defstruct binary-set-state :class :space :true-vars)

(defn make-binary-set-state [space true-vars]
  (doseq [x true-vars]  #(assert-is (member? x (:vars space))))
  (assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-set-state ::BinaryListState space (apply hash-set true-vars)))



;; Binary state spaces

(derive ::BinaryStateSpace ::angel.search.states/StateSpace)

(defstruct binary-state-space :class :vars)  ; :var-map)

(defn make-binary-state-space [vars] 
  "Make a binary state space from a set of variables"
  (assert-is (= vars (distinct vars)))
  (struct binary-state-space ::BinaryStateSpace (sort vars))) ;(to-array vars) (zipmap vars (nats))))


(defmethod list-states ::BinaryStateSpace [state-set]
  (map #(make-binary-set-state state-set %) (power-set (:vars state-set))))

(defmethod canonicalize ::BinaryStateSpace [state-set]
  state-set)  

(defmethod set-contains? ::BinaryStateSpace [state-set elt]
  (assert (= state-set (:space elt)))
  true)


;; Binary state sets

(derive ::BinaryStateSet ::angel.search.states/StateSet)
;(derive ::BinaryStateSpace ::BinaryStateSet)
;(defstruct binary-state-set :class :space :formula)
