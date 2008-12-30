;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.states.clj
;;
;;  Exports for states. 


(in-ns 'edu.berkeley.angel.search.states)

(derive ::StateSpace ::StateSet)

(defmulti list-states :class )
(defmethod list-states ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmulti count-states :class)
(defmethod count-states ::StateSet [state-set]
  (count (list-states state-set)))

(defmulti canonicalize :class)
(defmethod canonicalize ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmulti set-contains? #(:class %))
(defmethod set-contains? ::StateSet [state-set elt]
  (throw (UnsupportedOperationException. "Method not implemented")))


