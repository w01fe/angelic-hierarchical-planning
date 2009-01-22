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

;(defn difference2 "Like difference, but fast for big s2 and small s1." [s1 s2]
;  (reduce (fn [result item] (if (contains? s2 item) result (conj result item)))
;	  #{} s1))

(defn difference2 "Like difference, but fast for big s2 and small s1.  Only requires that s2 is a set." [s1 s2]
  (reduce (fn [result item] (if (contains? s2 item) (disj result item) result))
	  s1 s1))

(defn fast-difference "Like difference, but faster." [s1 s2]
  (if (or (not (set? s2))
	  (> (int (count s1)) (int (count s2))))
      (clojure.set/difference s1 s2)
    (difference2 s1 s2)))

(defn- fast-intersection- "Expects s1 and s2 sets, s1 bigger than s2." [s1 s2]
  (reduce (fn [result item] 
		(if (contains? s1 item) 
		  result 
		  (disj result item)))
	      s2 s2))

(defn fast-intersection "Like intersection, but faster." [s1 s2]
  (cond (not (set? s2)) 
          (reduce (fn [result item]
		    (if (contains? s1 item)
		        (conj result item)
		      result))
		  #{} s2)
	(> (int (count s1)) (int (count s2)))
	  (fast-intersection- s1 s2)
	:else
	  (fast-intersection- s2 s1)))

    
(defn fast-union "Like union, but faster." [s1 s2]
  (if (or (not (set? s2)) 
	  (> (int (count s1)) (int (count s2))))
      (reduce conj s1 s2)
    (reduce conj s2 s1)))


    

  



