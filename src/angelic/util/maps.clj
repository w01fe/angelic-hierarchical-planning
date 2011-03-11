(in-ns 'angelic.util)

(defn true-keys 
  "Return a lazy seq of the keys corresponding values satisfying pred in map."
  ([map] (true-keys identity map))
  ([pred map] (for [[k v] map :when (pred v)] k))
  {:test (fn [] (is (= #{ 3 4 6} (set (true-keys {1 nil 2 false 3 true 4 'asfd 5 nil 6 1})))))})

(defn identity-map [keys] (into {} (map vector keys keys)))

(defn map-map "Like map, but expects f to return pairs/map entries that are combined to make a map return value."
  [f & maps] 
  (into {} (apply map f maps)))
     ;(reduce #(conj %1 %2) {} (apply map f maps)))

(defn map-map1 "map-map, but specialized for 1 map argument."
  [f m]
  (persistent!
   (reduce (fn [m kv] (let [[k v] (f kv)] (assoc! m k v)))
           (transient {}) m)))


(defn map-keys [f m]
  (into {} (map (fn [[k v]] [(f k) v]) m)))

(defn map-vals [f m]
  (into {} (map (fn [[k v]] [k (f v)]) m)))

(defn filter-map [f m]
  (persistent! 
   (reduce (fn [m e] (if (f e) m (dissoc! m (key e))))
           (transient m) m)))

(defn assoc-f [m k f]
  (assoc m k
    (f (get m k))))

(defn assoc-cons [m k v]
  (assoc m k
    (cons v
      (get m k))))

(defn update!
  "'Updates' a value in a transient associative structure, where ks is a
  key and f is a function that will take the old value
  and any supplied args and return the new value, and returns a new
  nested structure."
  ([m k f & args]
     (assoc! m k (apply f (get m k) args))))


(defmacro lazy-get "Like get but lazy about default"
  [m k d]
  `(if-let [pair# (find ~m ~k)] 
       (val pair#)
     ~d))

(defn safe-get "Like get but throw an exception if not found"
  [m k] 
  (lazy-get m k (throw (IllegalArgumentException. (format "Key %s not found in %s" k m)))))

(defn safe-get-in 
  [m ks]
  (if (seq ks) 
      (recur (safe-get m (first ks)) (next ks))
    m))


(defn merge-agree "Like merge but returns nil if there are inconsistencies."
  ([] {})
  ([map] map)
  ([m1 m2 & maps]
     (when (every? (fn [[k v]] (= v (get m1 k v))) m2)
       (apply merge-agree (merge m1 m2) maps))))
  
(defn merge-disjoint [m1 m2]
  (let [ret (merge m1 m2)]
    (assert-is (= (count ret) (+ (count m1) (count m2))))
    ret))

; TODO: make more efficient ?
(defn merge-best [pred m & entry-seqs]
  (reduce (fn [m [k v]] 
	    (if-let [[ok ov] (find m k)]
	        (if (pred v ov) (assoc (dissoc m ok) k v) m)
	      (assoc m k v)))
	  m (apply concat entry-seqs)))

(defn merge-with-pred 
  "Like merge-with, but takes a predicate on values and keeps the best one.
   Also preserves the metadata on the key associated with the best value."
  ([pred] {})
  ([pred m] m)
  ([pred m & maps]
     (persistent!
      (reduce 
       (fn [tm1 [k v]]
         (if-let [[_ ov] (let [v (get tm1 k :G___123123)] (when-not (= v :G___123123) [nil v]))]
                          ;; Horrible hack since find doens't work on transients.
             (if (pred v ov) (assoc! (dissoc! tm1 k) k v) tm1)
           (assoc! tm1 k v)))
       (transient m) (apply concat maps)))))
	      
(import '[java.util HashMap])
(defn merge-all-with [f & ms]
  (let [h (HashMap.)]
    (doseq [m ms [k v] m] 
      (.put h k (cons v (.get h k))))
    (into {} (map-vals f h))))

(defn assoc-cat "Like assoc but for maps to lists"
  [m k v]
  (assoc m k (concat v (get m k))))
  
  ; TODO: replace with merge-with eventually
(defn merge-reduce "Combines maps, reducing sets of values with same key. Assumes nil value = not present.  The first map entry must be a real map, but the remaining arguments can be seqs of map entries/pairs."
  ([f ] {})
  ([f m1 & maps]
     (reduce (fn [m [k v]] 
	       (if-let [[_ v2] (find m k)]
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

(defn trans-map "Get a map representing the (safe) composition of m1 and m2" [m1 m2]
  (map-vals #(safe-get m2 %) m1))

(defmacro cache-with [^HashMap m key expr]
  `(let [m# ~m, key# ~key]
    (if (.containsKey m# key#) 
      (.get m# key#)
      (let [result# ~expr]
        (.put m# key# result#)
        result#))))

(defn pp-map [m]
  (doseq [[k v] m] (println "  " k "\t:" v)))

      
(comment   ; group-by in clojure.contrib.seq-utils.
(defn categorize 
  "Return a map keyed by the output of key-fn with vals from s"
  [key-fn s]
  (reduce (fn [m item] 
	    (let [k (key-fn item)]
	      (assoc m k (cons item (get m k ())))))
	  {} s))
	  )


      
#_
(defmacro for-map
  "Using bindings and filtering as provided by \"for\", efficiently build a map
   by repeatedly evaluating key-expr and val-expr.  If a key is repeated, the last
   value (according to \"for\" semantics) will be retained.  An optional symbol
   can be passed as a first argument, which will be bound to the transient map
   containing the entries produced so far."
  ([seq-exprs key-expr val-expr]
     (for-map (gensym "m") seq-exprs key-expr val-expr))
  ([m-sym seq-exprs key-expr val-expr]
     `(let [~m-sym (java.util.HashMap.)]
        (doseq ~seq-exprs
          (.put ~m-sym ~key-expr ~val-expr))
        (clojure.lang.PersistentHashMap/create ~m-sym))))


(defmacro for-map
  "Using bindings and filtering as provided by \"for\", efficiently build a map
   by repeatedly evaluating key-expr and val-expr.  If a key is repeated, the last
   value (according to \"for\" semantics) will be retained.  An optional symbol
   can be passed as a first argument, which will be bound to the transient map
   containing the entries produced so far."
  ([seq-exprs key-expr val-expr]
     `(for-map ~(gensym "m") ~seq-exprs ~key-expr ~val-expr))
  ([m-sym seq-exprs key-expr val-expr]
     `(let [m-atom# (atom (transient {}))]
        (doseq ~seq-exprs
          (let [~m-sym @m-atom#] (reset! m-atom# (assoc! ~m-sym ~key-expr ~val-expr))))
        (persistent! @m-atom#))))

#_
(defmacro for-map
  "Using bindings and filtering as provided by \"for\", efficiently build a map
   by repeatedly evaluating key-expr and val-expr.  If a key is repeated, the last
   value (according to \"for\" semantics) will be retained.  An optional symbol
   can be passed as a first argument, which will be bound to the transient map
   containing the entries produced so far."
  ([seq-exprs key-expr val-expr]
     (for-map (gensym "m") seq-exprs key-expr val-expr))
  ([m-sym seq-exprs key-expr val-expr]
     (let [step (fn step [recform exprs]
                  (if-not exprs
                 [true `(do (assoc! ~m-sym ~key-expr ~val-expr))]
                 (let [k (first exprs)
                       v (second exprs)]
                   (if (keyword? k)
                     (let [steppair (step recform (nnext exprs))
                           needrec (steppair 0)
                           subform (steppair 1)]
                       (cond
                         (= k :let) [needrec `(let ~v ~subform)]
                         (= k :while) [false `(if ~v
                                                (let [~m-sym ~subform]
                                                  ~(if needrec recform m-sym))
                                                ~m-sym)]
                         (= k :when) [false `(if ~v
                                               (let [~m-sym ~subform]
                                                 ~(if needrec recform m-sym))
                                               ~recform)]))
                     (let [seq- (gensym "seq_")
                           chunk- (with-meta (gensym "chunk_")
                                             {:tag 'clojure.lang.IChunk})
                           count- (gensym "count_")
                           i- (gensym "i_")
                           recform `(recur (next ~seq-) nil (int 0) (int 0) ~m-sym)
                           steppair (step recform (nnext exprs))
                           needrec (steppair 0)
                           subform (steppair 1)
                           recform-chunk 
                             `(recur ~seq- ~chunk- ~count- (unchecked-inc ~i-) ~m-sym)
                           steppair-chunk (step recform-chunk (nnext exprs))
                           subform-chunk (steppair-chunk 1)]
                       [true
                        `(loop [~seq- (seq ~v), ~chunk- nil,
                                ~count- (int 0), ~i- (int 0)
                                ~m-sym ~m-sym]
                           (if (< ~i- ~count-)
                             (let [~k (.nth ~chunk- ~i-)
                                   ~m-sym ~subform-chunk]  
                               ~(if needrec recform-chunk m-sym))
                             (if-let [~seq- (seq ~seq-)]
                               (if (chunked-seq? ~seq-)
                                 (let [c# (chunk-first ~seq-)]
                                   (recur (chunk-rest ~seq-) c#
                                          (int (count c#)) (int 0) ~m-sym))
                                 (let [~k (first ~seq-)
                                       ~m-sym ~subform]
                                   ~(if needrec recform m-sym)))
                               ~m-sym)))])))))]
        `(persistent! (let [~m-sym (transient {})] ~(nth (step nil (seq seq-exprs)) 1))))))