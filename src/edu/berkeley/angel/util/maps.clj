(in-ns 'edu.berkeley.angel.util)

(defn true-keys 
  "Return a lazy seq of the keys corresponding to logically true values in map."
  ([map] (for [[k v] map :when v] k))
  {:test (fn [] (is (= #{ 3 4 6} (set (true-keys {1 nil 2 false 3 true 4 'asfd 5 nil 6 1})))))})

(defn categorize 
  "Return a map keyed by the output of key-fn with vals from s"
  [key-fn s]
  (reduce (fn [m item] 
	    (let [k (key-fn item)]
	      (assoc m k (cons item (get m k ())))))
	  {} s))

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

(defn assoc-cat "Like assoc but for maps to lists"
  [m k v]
  (assoc m k (concat v (get m k))))