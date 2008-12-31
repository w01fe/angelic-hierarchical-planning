(in-ns 'edu.berkeley.angel.envs.states)

(defmulti list-states :class)
(defmulti count-states :class)
(defmulti canonicalize :class)
(defmulti set-contains? #(:class %))


(derive ::StateSpace ::StateSet)

(defmethod list-states ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmethod count-states ::StateSet [state-set]
  (count (list-states state-set)))

(defmethod canonicalize ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmethod set-contains? ::StateSet [state-set elt]
  (throw (UnsupportedOperationException. "Method not implemented")))


