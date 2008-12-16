;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.states.explicit.clj
;;
;;  Representations and simple functions for generic and explicit states, 
;;  state spaces, and sets of states.
;; 

(ns angel.search.states.explicit
 (:refer-clojure)
 (:use angel.search.states)
 )

(derive ::ExplicitStateSet ::angel.search.states/StateSpace)

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

