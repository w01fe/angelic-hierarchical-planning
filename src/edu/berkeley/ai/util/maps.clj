(in-ns 'edu.berkeley.ai.util)

(defn true-keys 
  "Return a lazy seq of the keys corresponding to logically true values in map."
  ([map] (for [[k v] map :when v] k))
  {:test (fn [] (is (= #{ 3 4 6} (set (true-keys {1 nil 2 false 3 true 4 'asfd 5 nil 6 1})))))})

(comment   ; group-by in clojure.contrib.seq-utils.
(defn categorize 
  "Return a map keyed by the output of key-fn with vals from s"
  [key-fn s]
  (reduce (fn [m item] 
	    (let [k (key-fn item)]
	      (assoc m k (cons item (get m k ())))))
	  {} s))
	  )

(defn map-map "Like a map for maps (/ seqs of map-entries)"
 [f m] (reduce #(conj %1 (f %2)) {} m))

(defmacro lazy-get "Like get but lazy about default"
  [m k d]
  `(if-let [pair# (find ~m ~k)] 
       (second pair#)
     ~d))

(defn safe-get "Like get but throw an exception if not found"
  [m k] 
  (lazy-get m k (throw (IllegalArgumentException. (format "Key %s not found" k)))))

(defn merge-agree "Like merge but returns nil if there are inconsistencies."
  ([] {})
  ([map] map)
  ([m1 m2 & maps]
     (when (every? (fn [[k v]] (= v (get m1 k v))) m2)
       (apply merge-agree (merge m1 m2) maps))))
  
(defn assoc-cat "Like assoc but for maps to lists"
  [m k v]
  (assoc m k (concat v (get m k))))

(defn merge-cat "Like merge but concatenates duplicate values (in rev. order.)"
  ([] {})
  ([map] map)
  ([m1 m2 & maps]
     (apply merge-cat 
	    (reduce (fn [m [k vs]] (assoc-cat m k vs))
		    {} (concat m1 m2))
	    maps)))

(defn map-map-cat "A map-map that concatenates duplicate values"
  [f m] (reduce (fn [m x] 
		  (let [[k v] (f x)]
		    (assoc-cat m k v)))
		{} m))
  