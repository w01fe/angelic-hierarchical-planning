(ns edu.berkeley.angel.util
  (:import (edu.berkeley.angel.util DelayedSeq)))

(defn member? 
  "Is item a member of seq?"
  ([item seq] (when-first [x seq] (or (= x item) (recur item (rest seq)))))
  ([item seq key test] (when-first [x seq] (or (test (key x) (key item)) (recur item (rest seq) key test))))
  {:test (fn [] (is (member? 1 '(2 1 3)))
	        (is (not (member? 1 '(2 -1 3))))
		(is (member? 1 '(2 -1 3) #(Math/abs %) =))
		(is (member? [1 2] '([3 4] [1 2])))
		(is (not (member? [1 2] '([3 4] [1 2]) identity ==))))})

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

(defn lazy-merge  "Lazily merge two sorted seqs in increasing order based on the supplied comparator, or compare otherwise"
  ([s1 s2] (lazy-merge s1 s2 compare))
  ([s1 s2 comparator]
     (cond (empty? s1) s2
	   (empty? s2) s1
	   (neg? (compare (first s1) (first s2))) (lazy-cons (first s1) (lazy-merge (rest s1) s2))
	   true                                   (lazy-cons (first s2) (lazy-merge s1 (rest s2))))))
     
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



;  ([arg &args]) `(lazy-cons  

;loop [arg args expr nil]
;			    (if (empty? (rest args)) 
;			      (first args)
;	true                 (lazy-

; (map (fn [[k v]] (list k (* (/ 6.0 10000) (count v)))) (categorize identity (take 10000 (repeatedly #(random-permutation '(1 2 3))))))