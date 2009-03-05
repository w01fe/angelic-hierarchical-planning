(in-ns 'edu.berkeley.ai.util)

(defstruct interval :left :left-open :right :right-open)

(defn make-interval [left left-open right right-open]
  (struct interval left left-open right right-open))


(defn interval-rand [interval]
  (let [l (:left interval) r (:right interval)]
    (assert-is (<= l r))
    (when (= l r) (assert (not (or (:left-open interval) (:right-open interval)))))
    (+ l (* (rand) (- r l)))))

(defn intersect-intervals [i1 i2]
  (let [l1 (:left i1) r1 (:right i1) lo1 (:left-open i1) ro1 (:right-open i1)
	l2 (:left i2) r2 (:right i2) lo2 (:left-open i2) ro2 (:right-open i2)]
    (struct interval 
	    (max l1 l2)
	    (cond (> l1 l2) lo1 (< l1 l2) lo2 :else (or lo1 lo2))
	    (min r1 r2)
	    (cond (< r1 r2) ro1 (> r1 r2) ro2 :else (or ro1 ro2)))))

(defn interval-contains? [i x]
  (and (or (> x (:left i))  (and (= x (:left i))  (not (:left-open i))))
       (or (< x (:right i)) (and (= x (:right i)) (not (:right-open i))))))

(defn interval-grid-points [i grid]
  (map #(* grid %)
       (range (int (if (:left-open i)
		       (Math/floor (+ 1 (/ (:left i) grid)))
		     (Math/ceil (/ (:left i) grid))))
	      (inc (if (:right-open i)
		       (int (Math/ceil (- (/ (:right i) grid) 1)))
		     (int (Math/floor (/ (:right i) grid))))))))

(def *real-line* (struct interval Double/NEGATIVE_INFINITY true Double/POSITIVE_INFINITY true))
