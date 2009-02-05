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
  (every? (to-set s2) s1))
  
(defn superset? [s1 s2]
  "Is s1 a superset of s2?"
  (every? (to-set s1) s2))
  
(defn proper-subset? [s1 s2]
  "Is s1 a proper subset of s2?"
  (let [s1 (to-set s1) s2 (to-set s2)]
    (and (not= (count s1) (count s2))
      (every? s2 s1))))
      
(defn proper-superset? [s1 s2]
  "Is s1 a proper superset of s2?"
  (let [s1 (to-set s1) s2 (to-set s2)]
    (and (not= (count s1) (count s2))
      (every? s1 s2))))




(defn union
  "Return a set that is the union of the input sets"
  ([] #{})
  ([s1] s1)
  ([s1 s2]
     (if (< (count s1) (count s2))
         (reduce conj s2 s1)
       (reduce conj s1 s2)))
  ([s1 s2 & sets] 
     (loop [biggest s1
	    biggest-size (count s1)
	    not-biggest nil
	    rest-colls (conj sets s2)]
       (if rest-colls
	 (let [first-coll (first rest-colls)
	       size (count first-coll)]
	   (if (> size biggest-size)
	       (recur first-coll size (cons biggest not-biggest) (rest rest-colls))
	     (recur biggest biggest-size (cons first-coll not-biggest) (rest rest-colls))))
	 (reduce into biggest not-biggest)))))


(defn- two-arg-intersection 
  "Take the intersection of sets s1 and s2; faster when s2 bigger than s1." 
  [s1 s2]
  (reduce (fn [result item]
	    (if (contains? s2 item)
	      result
	      (disj result item)))
	  s1 s1))

(defn intersection
  "Return a set that is the intersection of the input sets"
  ([s1] s1)
  ([s1 s2]
     (if (< (count s1) (count s2))
         (two-arg-intersection s1 s2)
       (two-arg-intersection s2 s1)))
  ([s1 s2 & sets] 
     (loop [smallest s1
	    smallest-size (count s1)
	    not-smallest nil
	    rest-colls (conj sets s2)]
       (if rest-colls
	 (let [first-coll (first rest-colls)
	       size (count first-coll)]
	   (if (< size smallest-size)
	       (recur first-coll size (cons smallest not-smallest) (rest rest-colls))
	     (recur smallest smallest-size (cons first-coll not-smallest) (rest rest-colls))))
	 (reduce two-arg-intersection smallest not-smallest)))))

(defn- two-arg-difference 
  "Return a set that is s1 without elements of s2."
  [s1 s2]
  (if (< (count s1) (count s2))
      (reduce (fn [result item] (if (contains? s2 item) (disj result item) result))
	      s1 s1)
    (reduce disj s1 s2)))

(defn difference
  "Return a set that is the first set without elements of the remaining sets"
  ([s1] s1)
  ([s1 s2] (two-arg-difference s1 s2))
  ([s1 s2 & sets] (reduce two-arg-difference s1 (conj sets s2))))


(defn union-coll [s coll]
  (into s coll))

(defn difference-coll [s coll]
  (reduce disj s coll))

(defn intersection-coll [s coll]
  (reduce (fn [result item]
	    (if (contains? s item)
	      (conj result item)
	      result))
	  #{} coll)) 
  
 	

	
	
  
  

    

  



