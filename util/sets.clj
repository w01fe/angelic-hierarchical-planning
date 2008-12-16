(in-ns 'angel.util)

(defn power-set
  "Returns a vector of possible subvectors of seq, in no particular order"
  ([seq]      (power-set seq [[]])) 
  ([seq sets] (if (empty? seq) 
		  sets 
		(recur (rest seq)
		       (lazy-cat sets (map #(cons (first seq) %) sets))))) 
  {:test (fn [] (is (= (power-set '(a b)) '[[] [a] [b] [b a]])))})