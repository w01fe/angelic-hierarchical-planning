(in-ns 'edu.berkeley.ai.util)

(defn rand-bool [p]
  (< (rand) p))

(defn sample-from [m]
  (loop [r (rand) m (seq m)]
    (if (or (<= r (val (first m))) (nil? (next m)))
        (ffirst m)
      (recur (- r (val (first m))) (next m)))))