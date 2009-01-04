(ns edu.berkeley.angel.util
  (:import (edu.berkeley.angel.util DelayedSeq)))

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

(defn first-maximal-element [f s]
  "Return the first element of s maximizing (f elt), throwing an exception if s empty."
  (if (empty? s) 
      (throw (IllegalArgumentException. "Empty seq has no maximal elt."))
    ((fn [f s max-elt max-val]
       (if (empty? s) 
	   max-elt
	 (let [elt (first s)
	       val (f elt)]
	   (if (> val max-val)
	       (recur f (rest s) elt val)
	     (recur f (rest s) max-elt max-val)))))
     f (rest s) (first s) (f (first s)))))

(defn random-maximal-element [f s]
  "Return a random element of s maximizing (f elt), throwing an exception if s empty."
  (random-element 
   ((fn [f s max-elts max-val]
      (if (empty? s) 
	  max-elts
	(let [elt (first s)
	      val (f elt)]
	   (cond (> val max-val) (recur f (rest s) [elt] val)
		 (= val max-val) (recur f (rest s) (cons elt max-elts) val)
                 :else  	 (recur f (rest s) max-elts max-val)))))
    f s '() Double/NEGATIVE_INFINITY)))

	   

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

(defn spread "Copied from clojure.core."
  [arglist]
  (cond
   (nil? arglist) nil
   (nil? (rest arglist)) (seq (first arglist))
   :else (cons (first arglist) (spread (rest arglist)))))

(defmacro lazy-seq "Create a lazy seq.  Expands to a bunch of lazy-conses."
  ([] nil)
  ([arg & args] `(lazy-cons ~arg (lazy-seq ~@args))))


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

(defn distinct-elts? [s]
  (let [s (seq s)]
    (= (count s) (count (distinct s)))))

(defn concat-elts "Lazily conctaenate a lazy seq of lazy seqs." [s] 
  (mapcat identity s))

(defn iterate-while [f x]
  (take-while identity (iterate f x)))

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