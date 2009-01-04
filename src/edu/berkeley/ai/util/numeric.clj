(in-ns 'edu.berkeley.angel.util)


(defn nats  
  "Return a lazy seq of the natural numbers"
  ([] (iterate inc 0))
  {:test (fn [] (is (= (take 5 (nats)) '(0 1 2 3 4))))})
 
 

