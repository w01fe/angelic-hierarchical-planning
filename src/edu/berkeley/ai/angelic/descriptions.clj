(in-ns 'edu.berkeley.ai.angelic)

(defmulti progress-optimistic (partial map :class))
(defmulti progress-pessimistic (partial map :class))

(defmulti regress-optimistic (partial map :class))
(defmulti regress-pessimistic (partial map :class))
