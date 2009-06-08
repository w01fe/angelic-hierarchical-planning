(ns edu.berkeley.ai.domains.nav-2d
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
 )



(defn preprocess-map 
  "Returns a new, hopefully fast/compact c-space free-fn"
  [width height free-fn radius]
  (let [offsets (for [dx (range (- radius) (inc radius)), dy (range (- radius) (inc radius))
		      :when (<= (+ (* dx dx) (* dy dy)) (* radius radius))]
		  [dx dy])]
    (fn [[x y]]
      (not-any? (fn [[dx dy]]
		  (let [nx (+ x dx)
			ny (+ y dy)]
		    (or (< nx 0) (>= nx width) (< ny 0) (>= ny height) (not (free-fn [nx ny])))))
		offsets))))


(let [f (util/path-local "nav_2d.pddl")]
  (defn make-nav-2d-strips-domain []
    (strips/read-strips-planning-domain f)))

 
(defn make-nav-2d-strips-env [free-fn [width height] [init-x init-y] [goal-x goal-y]]
  (strips/make-strips-planning-instance 
   "nav-2d"
   (make-nav-2d-strips-domain)
   {'xc (map #(util/symbol-cat "x" %) (range width))
    'yc (map #(util/symbol-cat "y" %) (range height))}
   (concat [['atx (util/symbol-cat "x" init-x)] ['aty (util/symbol-cat "y" init-y)]]
	   (map (fn [x] ['left-of (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	   (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height))
           (for [y (range height) x (range width) :when (free-fn [x y])] 
	     ['free (util/symbol-cat "x" x) (util/symbol-cat "y" y)])
   	   (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height)))
   [['atx (util/symbol-cat "x" goal-x)] ['aty (util/symbol-cat "y" goal-y)]]
   (fn [state]
     (let [pos [(util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1)
		(util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1)]]
	(util/str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		  (cond (= [x y] pos)             "O"
			(= [x y] [goal-x goal-y]) "G"
			(free-fn [x y])           "."
			:else                     "X")))))))))
    
(comment 
(def *test-map*
  [[0 1 0 0 0 0 0 0 1 0 0]
   [0 1 0 0 0 1 1 1 1 0 0]
   [0 1 0 1 0 0 0 0 1 1 0]
   [0 0 0 1 0 0 0 0 0 0 0]])

(def *test-map2*
  [[0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 1 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0]]))

(def *nav-2d-hierarchy*          (util/path-local "nav_2d.hierarchy"))




