(in-ns 'edu.berkeley.ai.util)

(import '(edu.berkeley.ai.util DelayedSeq))


(defn random-permutation [s]
  "Return a random permutation of this seq." 
  (let [arr (to-array s) len (alength arr)]
    (dotimes [i (dec len)]
      (let [r (+ i (rand-int (- len i))),
	    prev (aget arr i)]
	(aset arr i (aget arr r))
	(aset arr r prev)))
     (seq arr)))

(defn random-element [s]
  "Return a random element of this seq"
  (nth s (rand-int (count s))))

(defn maximal-elements [f s]
  "Return a seq of elements of s maximizing (f elt)."
  (when (seq s)
    (loop [max-elts [(first s)], 
	   max-val (f (first s)),
	   rest-elts (rest s)]
      (if (empty? rest-elts) 
	  max-elts
	(let [next-val (f (first rest-elts))]
	  (cond (< next-val max-val) (recur max-elts max-val (rest rest-elts))
		(= next-val max-val) (recur (cons (first rest-elts) max-elts) max-val (rest rest-elts))
		(> next-val max-val) (recur [(first rest-elts)] next-val (rest rest-elts))))))))

(defn first-maximal-element [f s]
  "Return the first element of s maximizing (f elt), throwing an exception if s empty."
  (first (make-safe (maximal-elements f s))))

(defn random-maximal-element [f s]
  "Return a random element of s maximizing (f elt), throwing an exception if s empty."
  (random-element (make-safe (maximal-elements f s))))
	   
(defn distinct-elts? [s] ;; TODO: remove if core changed
  (or (empty? s) (apply distinct? s)))

(defn lazy-merge  "Lazily merge two sorted seqs in increasing order based on the supplied comparator, or compare otherwise"
  ([s1 s2] (lazy-merge s1 s2 compare))
  ([s1 s2 comparator]
     (cond (empty? s1) s2
	   (empty? s2) s1
	   (neg? (compare (first s1) (first s2))) (lazy-cons (first s1) (lazy-merge (rest s1) s2))
	   true                                   (lazy-cons (first s2) (lazy-merge s1 (rest s2))))))
     
(defn cons-when "Like cons but ignores logically false items"
  [item seq]
  (if item (cons item seq) seq))

(defmacro lazy-cons-when "Like cons-when but lazy like lazy-cons"
  [item seq]
  `(let [item# ~item]
     (if item# (lazy-cons item# ~seq) ~seq)))

(defn map-when "Like map but discards logically false entries"
  [fn & seqs]
  (filter identity (apply map fn seqs)))

;(defn map-while "Like map but stops and returns nil on false result."

(defmacro lazy-seq "Create a lazy seq.  Expands to a bunch of lazy-conses."
  ([] nil)
  ([arg & args] `(lazy-cons ~arg (lazy-seq ~@args))))

(defn spread
  [arglist]
  (cond
   (nil? arglist) nil
   (nil? (rest arglist)) (seq (first arglist))
   :else (cons (first arglist) (spread (rest arglist)))))


(defmacro delay-seq "Create a collection representing this sequence, *really* without evaluating it until needed.  May pass elements before the seq that will be consed onto the front, like apply."
  ([] nil) 
  ([arg] `(DelayedSeq. (fn [] (seq ~arg))))
  ([arg & args] `(lazy-seq ~@(spread (cons arg args)))))

(defn seq->vector-pair [x]
  (cond (and (vector? x) (= (count x) 2) (coll? (second x))) x
	(coll? x)   [(first x) (rest x)]
	:else       [x nil]))

(defn enforce-seq [x]
  (cond (seq? x)  x
	(coll? x) (seq x)
	:else     (list x)))


(defn concat-elts "Lazily conctaenate a lazy seq of lazy seqs." [s] 
  (when (seq s) (lazy-cat (first s) (concat-elts (rest s)))))
;  (mapcat identity s))

(defn lazy-mapcat "Like mapcat but without the pain" [f s]
  (concat-elts (map f s)))

(defn iterate-while [f x]
  (take-while identity (iterate f x)))

(defn report-seq [msg coll]
  (lazy-cons
    (do (println "(first" msg (first coll) ")") (first coll))
    (do (println "(rest after" msg (first coll) ")")
      (when (rest coll)
        (report-seq msg (rest coll))))))

(defn partition-all "Lazily break s into partition-alls of length n (or less, for the final partition-all)."
  [n s]
  (when (seq s)
    (lazy-cons (take n s)
	       (partition-all n (drop n s)))))

(defn position-if [f s]
  (loop [s (seq s) i (int 0)]
    (when s
      (if (f (first s)) 
	  i
	(recur (rest s) (inc i))))))

(defn position [elt s]
  (loop [s (seq s) i (int 0)]
    (when s
      (if (= (first s) elt) 
	  i
	(recur (rest s) (inc i))))))

(defn positions-if [f s]
  (loop [s (seq s) i (int 0) pos []]
    (if s
        (if (f (first s)) 
	    (recur (rest s) (inc i) (conj pos i))
	  (recur (rest s) (inc i) pos))
      pos)))

(defn positions [elt s]
  (loop [s (seq s) i (int 0) pos []]
    (if s
        (if (= (first s) elt) 
	    (recur (rest s) (inc i) (conj pos i))
	  (recur (rest s) (inc i) pos))
      pos)))


(defn mevery? "Like every but takes multiple seq args like map."
  ([f & seqs]
     (or (some empty? seqs)
	 (and (apply f (map first seqs))
	      (recur f (map rest seqs))))))

(defn to-set [x]
  (if (set? x) x (set x))) 

(defn to-vec [x] 
  (if (vector? x) x (vec x)))








(comment   ; already in clojure.contrib with same name!
(defn separate "Like filter, but returns [true-elts false-elts]"
  [pred coll]
  [(filter pred coll) (filter (complement pred) coll)])
  )


;  ([arg &args]) `(lazy-cons  

;loop [arg args expr nil]
;			    (if (empty? (rest args)) 
;			      (first args)
;	true                 (lazy-

; (map (fn [[k v]] (list k (* (/ 6.0 10000) (count v)))) (categorize identity (take 10000 (repeatedly #(random-permutation '(1 2 3))))))


(comment ; already in clojure.contrib with name includes? (no keys though)
(defn member? 
  "Is item a member of seq?"
  ([item seq] (when-first [x seq] (or (= x item) (recur item (rest seq)))))
  ([item seq key test] (when-first [x seq] (or (test (key x) (key item)) (recur item (rest seq) key test))))
  {:test (fn [] (is (member? 1 '(2 1 3)))
	        (is (not (member? 1 '(2 -1 3))))
		(is (member? 1 '(2 -1 3) #(Math/abs %) =))
		(is (member? [1 2] '([3 4] [1 2])))
		(is (not (member? [1 2] '([3 4] [1 2]) identity ==))))})
    )

;     (comment ; already in contrib    (but broken)
    (defn my-combinations "Take a seq of seqs and return a lazy list of ordered combinations (pick 1 from each seq)" 
      [& seqs]
      (if (empty? seqs) '(())
        (for [item (first seqs)
	      rest (apply my-combinations (rest seqs))]
	  (cons item rest))))
;          (map #(cons item %) (combinations (rest seqs))))))
       ; )



       (comment ; not needed 
       (import '(java.util HashSet))
       (defn distinct-elts? "Are all of the elements of this sequence distinct?  Works on infinite sequences with repititions, making 
                             it useful for, e.g., detecting cycles in graphs." 
         [s]
         (let [hs (HashSet.)]
           (loop [s (seq s)]
             (cond (empty? s)                    true
       	    (.contains hs (first s))        false
                   :else (do (.add hs (first s)) (recur (rest s)))))))
       	  )

       (comment ; old version
       (defn distinct-elts? [s]
         (let [s (seq s)]
           (= (count s) (count (distinct s)))))
         )
