(ns edu.berkeley.ai.util.intervals
  (:use edu.berkeley.ai.util)
  )

(defstruct interval :left :left-open :right :right-open)

(defn make-interval [left left-open right right-open]
  (struct interval left left-open right right-open))

(def *real-line* (struct interval Double/NEGATIVE_INFINITY true Double/POSITIVE_INFINITY true))

(defn make-point-interval [x] (make-interval x false x false))

(defn interval-empty? [interval]
  (or (< (:right interval) (:left interval))
      (and (= (:right interval) (:left interval))
	   (or (:left-open interval) (:right-open interval)))))

(defn interval-point [interval]
  (and (= (:left interval) (:right interval))
       (not (:left-open interval))
       (not (:right-open interval))
       (:left interval)))

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

(defn interval-rand [interval]
  (let [l (:left interval) r (:right interval)]
    (assert-is (not (interval-empty? interval)))
    (+ l (* (rand) (- r l)))))

(defn intersect-intervals [i1 i2]
  (let [l1 (:left i1) r1 (:right i1) lo1 (:left-open i1) ro1 (:right-open i1)
	l2 (:left i2) r2 (:right i2) lo2 (:left-open i2) ro2 (:right-open i2)]
    (struct interval 
	    (max l1 l2)
	    (cond (> l1 l2) lo1 (< l1 l2) lo2 :else (or lo1 lo2))
	    (min r1 r2)
	    (cond (< r1 r2) ro1 (> r1 r2) ro2 :else (or ro1 ro2)))))

(defn add-intervals [i1 i2]
  (make-interval (+ (:left i1) (:left i2))
		 (or (:left-open i1) (:left-open i2))
		 (+ (:right i1) (:right i2))
		 (or (:right-open i1) (:right-open i2))))
		 
(defn subtract-intervals [i1 i2]
  (make-interval (- (:left i1) (:right i2))
		 (or (:left-open i1) (:right-open i2))
		 (- (:right i1) (:left i2))
		 (or (:right-open i1) (:left-open i2))))

(defn multiply-intervals [i1 i2]
  (loop [l (+ 0 Double/POSITIVE_INFINITY) lo false r (+ 0 Double/NEGATIVE_INFINITY) ro false 
	 vs     (seq (for [[e1 o1] [[(:left i1) (:left-open i1)] [(:right i1) (:right-open i1)]]
			   [e2 o2] [[(:left i2) (:left-open i2)] [(:right i2) (:right-open i2)]]]
		       [(* e1 e2) (or o1 o2)]))]
    (if vs
        (let [[e o] (first vs)]
	  (recur 
	   (min e l)
	   (if (or (< e l) (and (not o) (= e l))) o lo)
	   (max e r)
	   (if (or (> e l) (and (not o) (= e r))) o ro)
	   (next vs)))
      (make-interval l lo r ro))))

(defn bisect-interval [i]
  (assert-is (not (interval-point interval)))
  (let [{:keys [left right left-open right-open]} i
	mid (/ (+ left right) 2)]
    [(make-interval left left-open mid false)
     (make-interval mid true       right right-open)]))








(comment 
;; Convex Polytopes

(defmulti polytope-intersection (fn [t1 t2] [(:class t1) (:class t2)]))
(defmulti polytope-empty?       :class)



(derive ::Orthotope ::Polytope)
(defstruct orthotope :class :imap)  ; i-map is map from vars to intervals

(defn make-orthotope [imap] (struct orthotope ::Orthotope imap))

(defmethod polytope-intersection [::Orthotope ::Orthotope] [p1 p2] 
  (make-orthotope (merge-with intersect-intervals (:imap p1) (:imap p2))))

(defmethod polytope-empty? ::Orthotope [p]
  (some interval-empty? (vals (:imap p))))
)