(in-ns 'edu.berkeley.ai.angelic)

;; Methods for descriptions

(defmulti progress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti progress-pessimistic (fn [val desc] [(:class val) (:class desc)]))

(defmulti regress-optimistic (fn [val desc] [(:class val) (:class desc)]))
(defmulti regress-pessimistic (fn [val desc] [(:class val) (:class desc)]))



