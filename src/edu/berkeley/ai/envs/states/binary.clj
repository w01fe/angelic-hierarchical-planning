(ns edu.berkeley.angel.envs.states.binary
 (:refer-clojure)
 (:use edu.berkeley.angel.envs.states [edu.berkeley.angel.util :as util] )
 )



;; Binary state spaces

(derive ::BinaryStateSpace ::edu.berkeley.angel.envs.states/StateSpace)

(defstruct binary-state-space :class :vars) 

(defn make-binary-state-space [vars] 
  "Make a binary state space from a set of variables"
  (assert-is (= vars (distinct vars)))
  (struct binary-state-space ::BinaryStateSpace (sort vars))) 


(defmethod list-states ::BinaryStateSpace [state-set]
  (power-set (:vars state-set)))

(defmethod canonicalize ::BinaryStateSpace [state-set]
  state-set)  

(defmethod set-contains? ::BinaryStateSpace [state-set elt]
  (every? (:vars state-set) elt))






;; Binary state sets

;(derive ::BinaryStateSet ::edu.berkeley.angel.envs.states/StateSet)
;(derive ::BinaryStateSpace ::BinaryStateSet)
;(defstruct binary-state-set :class :space :formula)



(comment 
(derive ::BinaryVectorState ::BinaryState)
(derive ::BinarySetState ::BinaryState)

(defstruct binary-vector-state :class :space :true-vars)

(defn make-binary-vector-state [space true-vars]
  (doseq [x true-vars]  #(assert-is (member? x (:vars space))))
  (assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-vector-state ::BinaryVectorState space (apply vector true-vars)))


(defstruct binary-set-state :class :space :true-vars)

(defn make-binary-set-state [space true-vars]
  (doseq [x true-vars]  #(assert-is (member? x (:vars space))))
  (assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-set-state ::BinaryVectorState space (apply hash-set true-vars)))
 )
