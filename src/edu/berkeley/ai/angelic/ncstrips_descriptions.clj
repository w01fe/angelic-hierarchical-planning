(ns edu.berkeley.ai.angelic.ncstrips-descriptions
  (:refer-clojure)
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.dnf-simple-valuations)
  )



(defmethod progress-optimistic [::DNFSimpleValuation ::NCSTRIPSDescription] [val desc]
  )

(defmethod progress-pessimistic [::DNFSimpleValuation ::NCSTRIPSDescription] [val desc]
  )

;(defmethod regress-optimistic (partial (map :class)))
;(defmethod regress-pessimistic (partial (map :class)))

