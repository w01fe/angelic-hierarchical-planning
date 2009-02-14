(in-ns 'edu.berkeley.ai.util)

(defn true-keys 
  "Return a lazy seq of the keys corresponding values satisfying pred in map."
  ([map] (true-keys identity map))
  ([pred map] (for [[k v] map :when (pred v)] k))
  {:test (fn [] (is (= #{ 3 4 6} (set (true-keys {1 nil 2 false 3 true 4 'asfd 5 nil 6 1})))))})

(defn map-map "Like map, but expects f to return pairs/map entries that are combined to make a map return value."
  [f & maps] (into {} (apply map f maps)))
     ;(reduce #(conj %1 %2) {} (apply map f maps)))

(defn map-vals [f m]
  (into {} (map (fn [[k v]] [k (f v)]) m)))

(defn assoc-cons [m k v]
  (assoc m k
    (cons v
      (get m k))))

(defmacro lazy-get "Like get but lazy about default"
  [m k d]
  `(if-let [pair# (find ~m ~k)] 
       (val pair#)
     ~d))

(defn safe-get "Like get but throw an exception if not found"
  [m k] 
  (lazy-get m k (throw (IllegalArgumentException. (format "Key %s not found" k)))))

(defn safe-get-in 
  [m ks]
  (if (seq ks) 
      (recur (safe-get m (first ks)) (rest ks))
    m))

(defn merge-agree "Like merge but returns nil if there are inconsistencies."
  ([] {})
  ([map] map)
  ([m1 m2 & maps]
     (when (every? (fn [[k v]] (= v (get m1 k v))) m2)
       (apply merge-agree (merge m1 m2) maps))))
  
(defn assoc-cat "Like assoc but for maps to lists"
  [m k v]
  (assoc m k (concat v (get m k))))
  
  ; TODO: replace with merge-with eventually
(defn merge-reduce "Combines maps, reducing sets of values with same key. Assumes nil value = not present.  The first map entry must be a real map, but the remaining arguments can be seqs of map entries/pairs."
  ([f ] {})
  ([f m1 & maps]
     (reduce (fn [m [k v]] 
	       (if-let [v2 (get m k)]
		   (assoc m k (f v2 v))
		 (assoc m k v)))
	     m1
	     (concat-elts maps))))

(defn restrict-map [m s]
  "Remove all keys from m not in s."
  (let [s (to-set s)]
    (reduce (fn [result item]
	      (if (contains? s item)
		  result
		(dissoc result item)))
	    m (keys m))))
      
(defn keyset [m] (set (keys m)))

      
(comment   ; group-by in clojure.contrib.seq-utils.
(defn categorize 
  "Return a map keyed by the output of key-fn with vals from s"
  [key-fn s]
  (reduce (fn [m item] 
	    (let [k (key-fn item)]
	      (assoc m k (cons item (get m k ())))))
	  {} s))
	  )


      
