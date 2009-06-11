(ns edu.berkeley.ai.domains.nav-2d
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
 )




(let [f (util/path-local "nav_2d.pddl")]
  (defn make-nav-2d-strips-domain []
    (strips/read-strips-planning-domain f)))

 
(defn make-nav-2d-strips-env 
  "map-fn takes [x y] pair, returns :free, :border, or :occupied"
  [map-fn [width height] [init-x init-y] [goal-x goal-y]]
  (util/assert-is (= :free (map-fn [init-x init-y])))
  (util/assert-is (= :free (map-fn [goal-x goal-y])))
  (strips/make-strips-planning-instance 
   "nav-2d"  
   (make-nav-2d-strips-domain)
   {'xc (map #(util/symbol-cat "x" %) (range width))
    'yc (map #(util/symbol-cat "y" %) (range height))}
   (concat [['atx (util/symbol-cat "x" init-x)] ['aty (util/symbol-cat "y" init-y)]]
	   (map (fn [x] ['left-of (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	   (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height))
           (for [y (range height) x (range width) :when (= :border (map-fn [x y]))] 
	     ['border (util/symbol-cat "x" x) (util/symbol-cat "y" y)]))
   [['atx (util/symbol-cat "x" goal-x)] ['aty (util/symbol-cat "y" goal-y)]]
   (fn [state]
     (let [pos [(util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1)
		(util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1)]]
	(util/str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		  (cond (= [x y] pos)                "O"
			(= [x y] [goal-x goal-y])    "G"
			(= (map-fn [x y]) :border)   "X"
			(= (map-fn [x y]) :occupied) "@"
			:else                     ".")))))))))
   
(defn repurpose-nav-2d-strips-env [env [init-x init-y] [goal-x goal-y]]
  ; init-atoms, goal-atoms, always-true-atoms, const-pred-map
  (let [old-cpm      (util/safe-get env :const-pred-map)
	old-goal-atx (first (util/safe-get old-cpm 'goal-atx))
	old-goal-aty (first (util/safe-get old-cpm 'goal-aty))
	new-goal-atx ['goal-atx (util/symbol-cat "x" goal-x)]
	new-goal-aty ['goal-aty (util/symbol-cat "y" goal-y)]]
    (assoc env 
      :init-atoms [['atx (util/symbol-cat "x" init-x)] ['aty (util/symbol-cat "y" init-y)]]
      :goal-atoms [['atx (util/symbol-cat "x" goal-x)] ['aty (util/symbol-cat "y" goal-y)]]
      :always-true-atoms (conj (disj (util/safe-get env :always-true-atoms) old-goal-atx old-goal-aty)
			       new-goal-atx new-goal-aty)
      :const-pred-map    (assoc old-cpm 'goal-atx #{new-goal-atx} 'goal-aty #{new-goal-aty}))))



(comment 
(def *test-map*
  [[0 1 0 0 0 0 0 0 1 0 0]
   [0 1 0 0 0 1 1 1 1 0 0]
   [0 1 0 1 0 0 0 0 1 1 0]
   [0 0 0 1 0 0 0 0 0 0 0]])

(def *test-map2*
  [[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 1 0 0 0 0 0 0 0]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
   [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]]))

(def *nav-2d-hierarchy*          (util/path-local "nav_2d.hierarchy"))



























(comment 
(defn preprocess-map 
  "Returns a new, hopefully fast/compact c-space free-fn"
  [width height free-fn radius]
  (let [width (int width)
	height (int height)
	radius (int radius)
	offsets (for [dx (range (- radius) (inc radius)), dy (range (- radius) (inc radius))
		      :when (<= (+ (* dx dx) (* dy dy)) (* radius radius))]
		  [dx dy])
	fill-map (make-array Boolean/TYPE (* height width))]
    (doseq [y (range height), x (range width)]
      (let [x (int x) y (int y)]
	(when (some (fn [[dx dy]]
		      (let [dx (int dx)
			    dy (int dy)
			    nx (+ x dx)
			    ny (+ y dy)]
			(or (< nx 0) (>= nx width) (< ny 0) (>= ny height) (not (free-fn [nx ny])))))
		offsets)
	  (aset-boolean fill-map (+ x (* y width)) true)))
;      (println x y (aget fill-map (idx-fn x y)))
      )
    (fn [[x y]]
      (let [x (int x) y (int y)]
	(and (aget fill-map (+ x (* y width)))
	     (some (fn [[dx dy]]
		     (let [dx (int dx) dy (int dy)
			   nx (+ x dx), ny (+ y dy)]
		       (if (and (>= nx 0) (< nx width) (>= ny 0) (< ny height) (not (aget fill-map (+ nx (* ny width)))))
			 true nil)))
		 [[-1 0] [1 0] [0 -1] [0 1]])))))) )

