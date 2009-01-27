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
  
(defn proper-subset? [s1 s2]
  "Is s1 a proper subset of s2?"
  (let [s1 (set s1) s2 (set s2)]
    (and (not= (count s1) (count s2))
      (every? s2 s1))))
      
(defn proper-superset? [s1 s2]
  "Is s1 a proper superset of s2?"
  (let [s1 (set s1) s2 (set s2)]
    (and (not= (count s1) (count s2))
      (every? s1 s2))))


(defn difference "Like clojure.set/difference, but faster.  
                  First arg must be a set."
  ([s] s)
  ([s & colls]
     (reduce 
      (fn [s1 s2]
	(if (or (not (set? s2))
		(> (int (count s1)) (int (count s2))))
	    (reduce disj s1 s2)
	  (reduce (fn [result item] 
		    (if (contains? s2 item) (disj result item) result))
		  s1 s1)))
      s colls)))

(defn- intersection- "Expects s1 and s2 sets, s1 bigger than s2." [s1 s2]
  (reduce (fn [result item] 
		(if (contains? s1 item) 
		  result 
		  (disj result item)))
	      s2 s2))

(defn intersection "Like clojure.set/intersection, but faster.
                    First arg must be a set."
  ([s] s)
  ([s & colls]
     (reduce 
      (fn [s1 s2]
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
      s colls)))

    
(defn union "Like union, but faster.  First arg must be a set." 
  ([] #{})
  ([s] s)
  ([s & colls]
     (reduce 
      (fn [s1 s2]
	(if (or (not (set? s2)) 
		(> (int (count s1)) (int (count s2))))
  	    (reduce conj s1 s2)
	  (reduce conj s2 s1)))
      s colls)))


    

  



