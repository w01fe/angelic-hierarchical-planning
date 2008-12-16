(ns angel.util
  (:refer-clojure)
  )

(defn member? 
  "Is item a member of seq?"
  ([item seq] (when-first [x seq] (or (= x item) (recur item (rest seq)))))
  ([item seq key test] (when-first [x seq] (or (test (key x) (key item)) (recur item (rest seq) key test))))
  {:test (fn [] (is (member? 1 '(2 1 3)))
	        (is (not (member? 1 '(2 -1 3))))
		(is (member? 1 '(2 -1 3) #(Math/abs %) =))
		(is (member? [1 2] '([3 4] [1 2])))
		(is (not (member? [1 2] '([3 4] [1 2]) identity ==))))})

(defn random-permutation [s]
  "Return a random permutation of this seq." 
  (let [arr (to-array s) len (alength arr)]
    (dotimes [i (dec len)]
      (let [r (+ i (rand-int (- len i))),
	    prev (aget arr i)]
	(aset arr i (aget arr r))
	(aset arr r prev)))
     (seq arr)))

; (map (fn [[k v]] (list k (* (/ 6.0 10000) (count v)))) (categorize identity (take 10000 (repeatedly #(random-permutation '(1 2 3))))))