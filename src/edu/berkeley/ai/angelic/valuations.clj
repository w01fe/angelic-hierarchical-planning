(in-ns 'edu.berkeley.ai.angelic)

(defmulti make-initial-valuation (fn [type env] type))

(defmulti get-valuation-lower-bound :class)
(defmulti get-valuation-upper-bound :class)
(defmulti dead-end-valuation? :class)

(defmulti restrict-valuation (fn [val condition] [(:class val) (:class condition)]))


