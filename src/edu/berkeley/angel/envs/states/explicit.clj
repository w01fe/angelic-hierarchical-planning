(ns edu.berkeley.angel.envs.states.explicit
 (:refer-clojure)
 (:use edu.berkeley.angel.envs.states)
 )

(derive ::ExplicitStateSet ::edu.berkeley.angel.envs.states/StateSpace)

(defstruct explicit-state-set :class :states)

(defn make-explicit-state-set [states]
  "Make a state set from an explicit seq of states."
  (struct explicit-state-set ::ExplicitStateSet (apply sorted-set states)))


(defmethod list-states ::ExplicitStateSet [state-set]
  (:states state-set))

(defmethod canonicalize ::ExplicitStateSet [state-set]
  state-set)

(defmethod set-contains? ::ExplicitStateSet [state-set elt] 
  (contains? (:states state-set) elt))

