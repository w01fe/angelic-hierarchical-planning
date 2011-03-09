(ns angelic.old.envs.states.binary
 (:require 
  [angelic.old.envs :as envs]
  [angelic.util :as util]))
 



;; Binary state spaces

(derive ::BinaryStateSpace ::envs/StateSpace)

(defstruct binary-state-space :class :vars :str-fn) 

(defn make-binary-state-space 
  "Make a binary state space from a set of variables"
  ([vars] (make-binary-state-space vars str))
  ([vars str-fn]
  (let [var-set (set vars)]
    (util/assert-is (= (count vars) (count var-set)) "Duplicate vars in %s" vars)
    (struct binary-state-space ::BinaryStateSpace var-set str-fn))))


(defmethod envs/list-states ::BinaryStateSpace [state-set]
  (util/power-set (:vars state-set)))

(defmethod envs/canonicalize ::BinaryStateSpace [state-set]
  state-set)  

(defmethod envs/set-contains? ::BinaryStateSpace [state-set elt]
  (every? (:vars state-set) elt))








;; Binary state sets

;(derive ::BinaryStateSet ::angelic.old.envs.states/StateSet)
;(derive ::BinaryStateSpace ::BinaryStateSet)
;(defstruct binary-state-set :class :space :formula)



(comment 
(derive ::BinaryVectorState ::BinaryState)
(derive ::BinarySetState ::BinaryState)

(defstruct binary-vector-state :class :space :true-vars)

(defn make-binary-vector-state [space true-vars]
  (doseq [x true-vars]  #(util/assert-is (member? x (:vars space))))
  (util/assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-vector-state ::BinaryVectorState space (apply vector true-vars)))


(defstruct binary-set-state :class :space :true-vars)

(defn make-binary-set-state [space true-vars]
  (doseq [x true-vars]  #(util/assert-is (member? x (:vars space))))
  (util/assert-is (= (seq true-vars) (distinct true-vars)))
  (struct binary-set-state ::BinaryVectorState space (apply hash-set true-vars)))
 )
