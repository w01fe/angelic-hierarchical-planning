(in-ns 'edu.berkeley.ai.util)

;(defn vec-map [f v]
;  (reduce (fn [v i] (assoc v i (f (nth v i)))) v (range (count v))))

;(defn coll-seq [#^clojure.lang.IPersistentCollection coll] (.seq coll))

(defn vec-map [f v]
  (reduce (fn [v item] (conj v (f item))) [] v))

(defn vec-filter [f v]
  (reduce (fn [v item] (if (f item) (conj v item) v)) [] v))

(defn vec-replace [m v]
  (reduce (fn [v item]
	    (conj v
	      (if-let [e (find m item)]
		(val e)
		item)))
	  [] v))






;(defn vec-map3 [f v]
;  (reduce (fn [v item] (conj v (f item))) [] (coll-seq v)))


(defn maximal-elements [f s]
  "Return a seq of elements of s maximizing (f elt)."
  (when (seq s)
    (loop [max-elts [(first s)], 
	   max-val (f (first s)),
	   rest-elts (next s)]
      (if (empty? rest-elts) 
	  max-elts
	(let [next-val (f (first rest-elts))]
	  (cond (< next-val max-val) (recur max-elts max-val (next rest-elts))
		(= next-val max-val) (recur (cons (first rest-elts) max-elts) max-val (next rest-elts))
		(> next-val max-val) (recur [(first rest-elts)] next-val (next rest-elts))))))))

(defn first-maximal-element [f s]
  "Return the first element of s maximizing (f elt), throwing an exception if s empty."
  (first (make-safe (maximal-elements f s))))

(defn random-maximal-element [f s]
  "Return a random element of s maximizing (f elt), throwing an exception if s empty."
  (rand-elt (make-safe (maximal-elements f s))))
	   
(defn distinct-elts? [s] ;; TODO: remove if core changed
  (or (empty? s) (apply distinct? s)))

(defn lazy-merge  "Lazily merge two sorted seqs in increasing order based on the supplied comparator, or compare otherwise"
  ([s1 s2] (lazy-merge s1 s2 compare))
  ([s1 s2 comparator]
     (cond (empty? s1) s2
	   (empty? s2) s1
	   (neg? (compare (first s1) (first s2))) (lazy-seq (cons (first s1) (lazy-merge (next s1) s2)))
	   true                                   (lazy-seq (cons (first s2) (lazy-merge s1 (next s2)))))))
     
(defn cons-when "Like cons but ignores logically false items"
  [item seq]
  (if item (cons item seq) seq))

(defmacro lazy-cons-when "Like cons-when but lazy like lazy-cons"
  [item seq]
  `(let [item# ~item]
     (if item# (lazy-seq (cons item# ~seq)) ~seq)))

(defn map-when "Like map but discards logically false entries"
  [fn & seqs]
  (filter identity (apply map fn seqs)))

;(defn map-while "Like map but stops and returns nil on false result."


(defn spread
  [arglist]
  (cond
   (nil? arglist) nil
   (nil? (next arglist)) (seq (first arglist))
   :else (cons (first arglist) (spread (next arglist)))))


(defn seq->vector-pair [x]
  (cond (and (vector? x) (= (count x) 2) (coll? (second x))) x
	(coll? x)   [(first x) (next x)]
	:else       [x nil]))

;(defn enforce-seq [x]
;  (cond (seq? x)  x
;	(coll? x) (seq x)
;	:else     (list x)))

;(defn any? [pred coll]
;  (when-let [s (seq coll)]
;    (or (pred (first s)) true)
;	(recur pred (rest s)))))

(defn seq-coll 
  "Make x a seq if it is a seq or coll, otherwise leave it alone. 
   Useful for normalizing, since (= [] nil) --> false"
  [x]
  (if (coll? x) (seq x) x))

(defn concat-elts "Lazily conctaenate a lazy seq of lazy seqs." [s] 
  (lazy-seq
    (when-let [s (seq s)]
      (lazy-cat (first s) (concat-elts (rest s))))))
;  (mapcat identity s))

(defn lazy-mapcat "Like mapcat but without the pain" [f s]
  (concat-elts (map f s)))

(defn iterate-while [f x]
  (take-while identity (iterate f x)))

(defn report-seq [msg coll]
  (lazy-seq (cons
    (do (println "(first" msg (first coll) ")") (first coll))
    (do (println "(next after" msg (first coll) ")")
      (when (next coll)
        (report-seq msg (next coll)))))))

;(comment 
(defn partition-all "Lazily break s into partition-alls of length n (or less, for the final partition-all)."
  [n s]
  (when (seq s)
    (lazy-seq (cons (take n s)
	       (partition-all n (drop n s))))))
;  )
(defn position-if [f s]
  (loop [s (seq s) i (int 0)]
    (when s
      (if (f (first s)) 
	  i
	(recur (next s) (inc i))))))

(defn position [elt s]
  (loop [s (seq s) i (int 0)]
    (when s
      (if (= (first s) elt) 
	  i
	(recur (next s) (inc i))))))

(defn positions-if [f s]
  (loop [s (seq s) i (int 0) pos []]
    (if s
        (if (f (first s)) 
	    (recur (next s) (inc i) (conj pos i))
	  (recur (next s) (inc i) pos))
      pos)))

(defn positions [elt s]
  (loop [s (seq s) i (int 0) pos []]
    (if s
        (if (= (first s) elt) 
	    (recur (next s) (inc i) (conj pos i))
	  (recur (next s) (inc i) pos))
      pos)))


(defn mevery? "Like every but takes multiple seq args like map."
  ([f & seqs]
     (or (some empty? seqs)
	 (and (apply f (map first seqs))
	      (recur f (map next seqs))))))

(defn to-set [x]
  (if (set? x) x (set x))) 

(defn to-vec [x] 
  (if (vector? x) x (vec x)))

(defn count-when [f c]
  (reduce (fn [v i] (if (f i) (inc v) v)) 0 c))

(defn reduce-key 
  ([f k c] (apply f (map k c)))
  ([f k init c] (reduce (fn [v i] (f v (k i))) init c)))

(defn sum-over [f c]
  (reduce (fn [v i] (+ v (f i))) 0 c))

(defn singleton? [c] 
  (= (count c) 1))

(defn singleton [c]
  (when (singleton? c) (first c)))

(defn safe-singleton [c]
  (assert-is (singleton? c))
  (first c))

;(defn find-first [p c]
;  (when-first [x c]
;     (if (p x) x (recur p (next c)))))


; (map (fn [[k v]] (list k (* (/ 6.0 10000) (count v)))) (categorize identity (take 10000 (repeatedly #(random-permutation '(1 2 3))))))


(comment ; already in clojure.contrib with name includes? (no keys though)
(defn member? 
  "Is item a member of seq?"
  ([item seq] (when-first [x seq] (or (= x item) (recur item (next seq)))))
  ([item seq key test] (when-first [x seq] (or (test (key x) (key item)) (recur item (next seq) key test))))
  {:test (fn [] (is (member? 1 '(2 1 3)))
	        (is (not (member? 1 '(2 -1 3))))
		(is (member? 1 '(2 -1 3) #(Math/abs %) =))
		(is (member? [1 2] '([3 4] [1 2])))
		(is (not (member? [1 2] '([3 4] [1 2]) identity ==))))})
    )


	(comment ; not needed in lazy branch
	(defmacro delay-seq "Create a collection representing this sequence, *really* without evaluating it until needed.  May pass elements before the seq that will be consed onto the front, like apply."
	  ([] nil) 
	  ([arg] `(DelayedSeq. (fn [] (seq ~arg))))
	  ([arg & args] `(lazy-seq ~@(spread (cons arg args)))))
	
	(defmacro lazy-seq "Create a lazy seq.  Expands to a bunch of lazy-conses."
	  ([] nil)
	  ([arg & args] `(lazy-cons ~arg (lazy-seq ~@args))))
	
	 )


