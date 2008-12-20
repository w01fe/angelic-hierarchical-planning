(in-ns 'edu.berkeley.angel.util)

(defmacro assert-is
  "Like assert, but prints some more info about the offending form (may multiple eval on error)"
  [form]
  `(when-not ~form
     (throw (Exception. (str "Got " '~form " as " (list ~@form))))))
