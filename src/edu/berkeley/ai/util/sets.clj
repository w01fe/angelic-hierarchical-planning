(in-ns 'edu.berkeley.ai.util)

(defn power-set
  "Returns a vector of possible subvectors of seq, in no particular order"
  ([seq]      (power-set seq [[]])) 
  ([seq sets] (if (empty? seq) 
		  sets 
		(recur (rest seq)
		       (lazy-cat sets (map #(cons (first seq) %) sets))))) 
  {:test (fn [] (is (= (power-set '(a b)) '[[] [a] [b] [b a]])))})
  
(defn subset? [s1 s2]
  "Is s1 a subset of s2?"
  (every? (set s2) s1))
  
(defn superset? [s1 s2]
  "Is s1 a superset of s2?"
  (every? (set s1) s2))
  
(defn proper_subset? [s1 s2]
  "Is s1 a proper subset of s2?"
  (let [s1 (set s1) s2 (set s2)]
    (and (not= (count s1) (count s2))
      (every? s2 s1))))
      
(defn proper_superset? [s1 s2]
  "Is s1 a proper superset of s2?"
  (let [s1 (set s1) s2 (set s2)]
    (and (not= (count s1) (count s2))
      (every? s1 s2))))


