(ns edu.berkeley.ai.util.intervals
  (:use edu.berkeley.ai.util
	[clojure.contrib.types :only (deftype)]
        [clojure.contrib.generic :only (root-type)])
  (:require [clojure.contrib.generic.arithmetic :as ga]
 ;           [clojure.contrib.generic.comparison :as gc]
            [clojure.contrib.generic.math-functions :as gm]))


(defstruct interval :left :left-open :right :right-open)

(deftype ::interval make-interval
  (fn [l lo r ro] (struct interval l lo r ro))
  (fn [i] (vals i)))

(derive ::interval root-type)


;(defn make-interval [left left-open right right-open]
;  (with-meta (struct interval left left-open right right-open)
;     {:type ::interval}))

(def *real-line* (make-interval Double/NEGATIVE_INFINITY true Double/POSITIVE_INFINITY true))

(defn make-point-interval [x] (make-interval x false x false))

(defn parse-interval 
  "Take a number, or [lb ub] expression where lb and ub can be nil, and produce
   an appropriate closed interval."
  [x] 
  (cond (number? x) (make-point-interval x)
	(nil? x) *real-line*
	(coll? x) (do (assert (<= (count x) 2))
		      (let [[l u] x]
			(make-interval (or l Double/NEGATIVE_INFINITY) (if l false true)
				       (or u Double/POSITIVE_INFINITY) (if u false true))))
	:else (throw (Exception. "I don't know how to make an interval out of " x))))

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
    (make-interval 
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

(defn negate-interval [i]
  (make-interval (- (:right i)) (:right-open i) (- (:left i)) (:left-open i)))

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

(defn scale-interval [i c]
  (let [l (:left i) r (:right i)]
    (if (>= c 0) (assoc i :left (* c l) :right (* c r))
	(make-interval (* r c) (:right-open i) (* l c) (:left-open i)))))
   
(defn abs-interval [i]
  (if (>= (:left i) 0) i
      (let [l (abs (:left i)) lo (:left-open i) r (:right i) ro (:right-open i)]
	(cond (= l r) 
	        (make-interval 0 false l (and lo ro))
	      (> l r) 
	        (make-interval 0 false l lo)
	      (< l r) 
	        (make-interval 0 false r ro)))))

(defn bisect-interval [i]
  (assert-is (not (interval-point interval)))
  (let [{:keys [left right left-open right-open]} i
	mid (/ (+ left right) 2)]
    [(make-interval left left-open mid false)
     (make-interval mid true       right right-open)]))


;;; Generic stuff

(defmethod ga/+ [::interval ::interval] [x y]
  (add-intervals x y))

(defmethod ga/+ [::interval root-type] [x y]
  (add-intervals x (make-point-interval y)))

(defmethod ga/+ [root-type ::interval] [x y]
  (add-intervals y (make-point-interval x)))


(defmethod ga/- ::interval [x]
  (negate-interval x))


(defmethod ga/* [::interval ::interval] [x y]
  (multiply-intervals x y))

(defmethod ga/* [::interval root-type] [x y]
  (scale-interval x y))

(defmethod ga/* [root-type ::interval] [x y]
  (scale-interval y x))


(defmethod gm/abs ::interval [i]
  (abs-interval i))




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