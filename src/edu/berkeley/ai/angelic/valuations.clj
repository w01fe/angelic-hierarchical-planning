(in-ns 'edu.berkeley.ai.angelic)

(defmulti get-valuation-lower-bound :class)
(defmulti get-valuation-upper-bound :class)
(defmulti dead-end-valuation? :class)

(defmulti restrict-valuation (partial map :class))
