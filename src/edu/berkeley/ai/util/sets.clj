(in-ns 'edu.berkeley.ai.util)

(defn power-set
  "Returns a lazy seq of possible subvectors of seq s."
  [s]
  (loop [s (seq s), sets [[]]]
    (if s 
        (recur (rest s) (lazy-cat sets (map #(conj % (first s)) sets)))
      sets)))
  
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


