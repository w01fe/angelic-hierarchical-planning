(ns angelic.old.envs.states.explicit
 (:require [angelic.old.envs :as envs])
 )

(derive ::ExplicitStateSet ::envs/StateSpace)

(defstruct explicit-state-set :class :states)

(defn make-explicit-state-set [states]
  "Make a state set from an explicit seq of states."
  (struct explicit-state-set ::ExplicitStateSet (apply sorted-set states)))


(defmethod envs/list-states ::ExplicitStateSet [state-set]
  (:states state-set))

(defmethod envs/canonicalize ::ExplicitStateSet [state-set]
  state-set)

(defmethod envs/set-contains? ::ExplicitStateSet [state-set elt] 
  (contains? (:states state-set) elt))

