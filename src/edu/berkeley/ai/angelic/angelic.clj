(in-ns 'edu.berkeley.ai.angelic)


; Impelmenters of progression are expected to increment the appropriate counters:

(def *op-counter* (util/sref 0))
(def *pp-counter* (util/sref 0))

(defn reset-op-counter [] (util/sref-set! *op-counter* 0))
(defn reset-pp-counter [] (util/sref-set! *pp-counter* 0))

(defn reset-progression-counters [] (reset-op-counter) (reset-pp-counter))
