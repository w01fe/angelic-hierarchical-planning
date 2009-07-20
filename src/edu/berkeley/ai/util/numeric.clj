(in-ns 'edu.berkeley.ai.util)


(defn nats  
  "Return a lazy seq of the natural numbers"
  ([] (iterate inc 0))
  {:test (fn [] (is (= (take 5 (nats)) '(0 1 2 3 4))))})
 
(defn mean [& coll]
  (/ (reduce + coll) (count coll)))

(defn median [coll]
  (let [coll (sort coll)
	n    (count coll)]
    (if (odd? n)
        (nth coll (/ (dec n) 2))
      (/ (+ (nth coll (/ n 2)) (nth coll (dec (/ n 2)))) 2))))

(defn geometric-mean [& coll]
  (Math/pow (double (reduce * coll)) (/ 1.0 (count coll)))) 

(defn abs [x] (if (neg? x) (- x) x))

(defn indicator [x] (if x 1 0))

(defn counter-from [x]
  (let [c (sref (dec x))]
     #(sref-up! c inc)))