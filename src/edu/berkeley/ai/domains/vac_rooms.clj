(ns edu.berkeley.ai.domains.vac-rooms
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
 )



(let [f (util/path-local "vac_rooms.pddl")]
  (defn make-vac-rooms-strips-domain []
    (strips/read-strips-planning-domain f)))

(set! *warn-on-reflection* true)

(defn make-vac-rooms-strips-env 
  "Rooms is list of [[minx miny] [maxx maxy]] - cannot overlap
   Doors is list of [[x1 y1] [x2 y2]] - must be in different rooms, will be bidi
   By default, all room squares (and no others) are dirty by default, must be cleaned."   
  [width height rooms doors initial-pos]
  (let [rooms (util/indexed rooms)
	#^"[[Ljava.lang.Object;" arr (make-array Object height width)]
    (doseq [[i [[sx sy] [lx ly]]] rooms
	    x (range sx (inc lx))
	    y (range sy (inc ly))]
      (assert (nil? (aget arr (int y) (int x))))
      (aset arr (int y) (int x) i))
    (strips/make-strips-planning-instance 
     "vac-rooms"
     (make-vac-rooms-strips-domain)
     {'xc (map #(util/symbol-cat "x" %) (range width))
      'yc (map #(util/symbol-cat "y" %) (range height))
      'room (map #(util/symbol-cat "r" %) (map first rooms))}
     (concat [['atx (util/symbol-cat "x" (first initial-pos))] 
	      ['aty (util/symbol-cat "y" (second initial-pos))]]
	     [['in-room (util/symbol-cat "r" (int (aget arr (int (second initial-pos)) (int (first initial-pos)))))]]
	     (apply concat
	      (for [[r [[sx sy] [lx ly]]] rooms]
		(concat
		 [['rooml (util/symbol-cat "r" r) (util/symbol-cat "x" sx)]
		  ['roomr (util/symbol-cat "r" r) (util/symbol-cat "x" lx)]
		  ['roomt (util/symbol-cat "r" r) (util/symbol-cat "y" sy)]
		  ['roomb (util/symbol-cat "r" r) (util/symbol-cat "y" ly)]]
		 (for [x (range sx (inc lx))]
		   ['roomx (util/symbol-cat "r" r) (util/symbol-cat "x" x)])
		 (for [y (range sy (inc ly))]
		   ['roomy (util/symbol-cat "r" r) (util/symbol-cat "y" y)]))))
	     (apply concat
	      (for [[[x1 y1] [x2 y2]] doors]
	       (let [r1 (int (aget arr (int y1) (int x1)))
		     r2 (int (aget arr (int y2) (int x2)))]
		 [['hall (util/symbol-cat "x" x1) (util/symbol-cat "y" y1) (util/symbol-cat "r" r2) 
		   (util/symbol-cat "x" x2) (util/symbol-cat "y" y2)]
		  ['hall (util/symbol-cat "x" x2) (util/symbol-cat "y" y2) (util/symbol-cat "r" r1) 
		   (util/symbol-cat "x" x1) (util/symbol-cat "y" y1)]])))
	     (map (fn [x] ['left-of (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	     (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height)))
     (for [y (range height) x (range width) 
	   :when (aget arr y x)]
       ['clean (util/symbol-cat "x" x) (util/symbol-cat "y" y)]) 
     (fn [state]
       (let [pos [(util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1)
		  (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1)]]
	 (util/str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		(let [reg (aget arr y x)
		      clean? (when reg (contains? state ['clean (util/symbol-cat "x" x)(util/symbol-cat "y" y)]))]
		  (cond (not reg) \X
			(= [x y] pos) (if clean? \O \o)
			clean?        \ 
                        :else         (first (str reg)))))))))))))

  

(set! *warn-on-reflection* false)

(comment

 
(defn make-nav-switch-strips-env [width height switch-coords initial-pos initial-hor? goal-pos]
  (strips/make-strips-planning-instance 
   "nav-switch"
   (make-nav-switch-strips-domain)
   {'xc (map #(util/symbol-cat "x" %) (range width))
    'yc (map #(util/symbol-cat "y" %) (range height))}
   (concat (when initial-hor? '[[horiz]])
	   [['atx (util/symbol-cat "x" (first initial-pos))] ['aty (util/symbol-cat "y" (second initial-pos))]]
	   (map (fn [pos] ['switch-at (util/symbol-cat "x" (first pos)) (util/symbol-cat "y" (second pos))]) switch-coords)
	   (map (fn [x] ['left-of (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	   (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height)))
   [['atx (util/symbol-cat "x" (first goal-pos))] ['aty (util/symbol-cat "y" (second goal-pos))]]
   (fn [state]
     (let [pos [(util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1)
		(util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1)]
	   hor? (contains? state '[horiz])]
	(util/str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		(let [coord [x y]]
		  (if (contains? (set switch-coords)  coord)
		      (if (= coord pos) \b \s)
		    (if (= coord pos) \o (if hor? \- \|))))))))))
   ))
    

(def *nav-switch-hierarchy*          (util/path-local "nav_switch.hierarchy"))
(def *nav-switch-hierarchy-unguided*          (util/path-local "nav_switch_unguided.hierarchy"))
;(def *nav-switch-hierarchy2*         (util/path-local "nav_switch2.hierarchy"))
(def *nav-switch-old-hierarchy* (util/path-local "nav_switch_old.hierarchy"))
(def *nav-switch-flat-hierarchy*          (util/path-local "nav_switch_flat.hierarchy"))



(defn make-flat-nav-switch-heuristic [env]
  (let [goal (envs/get-goal env)
	pos  (envs/get-positive-conjuncts goal)
	goal-x (util/desymbolize (second (util/make-safe (util/find-first #(= (first %) 'atx) pos))) 1)
	goal-y (util/desymbolize (second (util/make-safe (util/find-first #(= (first %) 'aty) pos))) 1)]
    (util/assert-is (= (count pos) 2))
   (fn [state] 
     (* -2 (+ (util/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) goal-x)) 
	      (util/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) goal-y)))))))


(defn- get-and-check-sol [env]
  (map :name
    (first
     (envs/check-solution env
       (edu.berkeley.ai.search.algorithms.textbook/a-star-search 
	(edu.berkeley.ai.search/make-initial-state-space-node 
	 env   
	 (constantly 0)))))))

(util/deftest flat-nav-switch
  (util/testing "non-strips"
    (util/is (= ['left 'flip 'down]
     (get-and-check-sol 
      (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1])))))
  (util/testing "strips"
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/constant-predicate-simplify
       (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])))))
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/flatten-strips-instance
       (strips/constant-predicate-simplify
	(make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))))))



  
  )
(comment 
  (u util search search.algorithms.textbook domains.nav-switch)
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0) 100 1))
  (map :name (first (a-star-search (state-space-search-node (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0)))))
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) #(reduce + (map (comp (fn [x] (* -2 (Math/abs x))) -) (:pos %) [0 1])) 10 1))

  (dotimes [_ 3] (time (map :name (first (a-star-search (state-space-search-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))))
  ; right now STRIPS is about equal in speed to hand-coded, with new successor generator!
    ; TODO: reachability analysis (planning graph?)

  (time (second (a-star-search (make-initial-state-space-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))
 ; "Elapsed time: 3596.095 msecs"

  (time (second (a-star-search (make-initial-state-space-node (constant-predicate-simplify (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])) (constantly 0)))))

  )
