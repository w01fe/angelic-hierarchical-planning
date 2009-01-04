(in-ns 'edu.berkeley.ai.envs.states)

(defmulti list-states :class)
(defmulti count-states :class)
(defmulti canonicalize :class)
(defmulti set-contains? (fn [state-set elt] (:class state-set)))
(defmulti state-str (fn [state-set elt] (:class state-set)))


(derive ::StateSpace ::StateSet)

(defmethod list-states ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmethod count-states ::StateSet [state-set]
  (count (list-states state-set)))

(defmethod canonicalize ::StateSet [state-set]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmethod set-contains? ::StateSet [state-set elt]
  (throw (UnsupportedOperationException. "Method not implemented")))

(defmethod state-str ::StateSet [state-set elt]
  ((or (:str-fn state-set) str) elt))



(defn make-state-set [str-fn] 
  {:class ::StateSet, :str-fn str-fn})

