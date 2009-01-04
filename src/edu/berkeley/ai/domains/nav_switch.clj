(ns edu.berkeley.angel.domains.nav-switch
 (:refer-clojure)
 (:use clojure.contrib.str-utils [edu.berkeley.angel.util :as util] edu.berkeley.angel.envs edu.berkeley.angel.envs.states)
 )

;(derive ::NavSwitch ::Environment)
;(defstruct nav-switch-env :class :height :width :switch-coords :initial-pos :initial-hor?)



(defstruct nav-switch-state :pos :hor?) 

(def +flip-reward+     -1)
(def +goodmove-reward+ -2)
(def +badmove-reward+  -4)

(defn legal-coord?- [coord height width]
  (and (>= (first coord) 0)
       (< (first coord) width)
       (>= (second coord) 0)
       (< (second coord) height)))
  

(defn make-nav-switch-env [height width switch-coords initial-pos initial-hor? goal-pos]
  (let [switch-coords (set (map seq switch-coords))
	initial-hor? (truthify initial-hor?)]
    (assert-is (pos? height))
    (assert-is (pos? width))
    (doseq [coord (cons initial-pos switch-coords)]
      (assert-is (legal-coord?- coord height width)))
    (make-environment 
     (struct nav-switch-state initial-pos initial-hor?)
     (make-state-set
      (fn [state]
	(str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		(let [coord [x y]]
		  (if (contains? switch-coords  coord)
		      (if (= coord (:pos state)) \b \s)
		    (if (= coord (:pos state)) \o (if (:hor? state) \- \|))))))))))
     (make-action-space 
      (fn [state]
	(let [coord (:pos state)]
	  (lazy-cons-when 
	   (when (contains? switch-coords coord)
	     (make-action 'flip #(vector (struct nav-switch-state (:pos %) (not (:hor? %))) +flip-reward+)))
	   (for [[name delta] [['left [-1 0]] ['right [1 0]] ['up [0 -1]] ['down [0 1]]]
		 :when (legal-coord?- (map + coord delta) height width)]
	     (make-action name #(vector (struct nav-switch-state (map + (:pos %) delta) (:hor? %))
					(if (xor (zero? (first delta)) (:hor? %)) +goodmove-reward+ +badmove-reward+))))))))
     (make-goal #(= (:pos %) goal-pos)))))

(comment 
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0) 100 1))
  (map :name (first (a-star-search (state-space-search-node (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0)))))
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) #(reduce + (map (comp (fn [x] (* -2 (Math/abs x))) -) (:pos %) [0 1])) 10 1))
  )