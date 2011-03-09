(ns angelic.old.domains.nav-switch
 (:require [angelic.util :as util] [angelic.old  [envs :as envs]] 
           [angelic.old.envs.strips :as strips])
 )




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
	initial-hor? (util/truthify initial-hor?)]
    (util/assert-is (pos? height))
    (util/assert-is (pos? width))
    (doseq [coord (cons initial-pos switch-coords)]
      (util/assert-is (legal-coord?- coord height width)))
    (envs/make-environment 
     (struct nav-switch-state initial-pos initial-hor?)
     (envs/make-state-set
      (fn [state]
	(util/str-join "\n"
	  (for [y (range height)]
	    (apply str
	      (for [x (range width)]
		(let [coord [x y]]
		  (if (contains? switch-coords  coord)
		      (if (= coord (:pos state)) \b \s)
		    (if (= coord (:pos state)) \o (if (:hor? state) \- \|))))))))))
     (envs/make-enumerated-action-space 
      (cons (envs/make-action 'flip #(vector (struct nav-switch-state (:pos %) (not (:hor? %))) +flip-reward+) 
			  (envs/make-simple-condition #(contains? switch-coords (:pos %))))
	    (for [[name delta] [['left [-1 0]] ['right [1 0]] ['up [0 -1]] ['down [0 1]]]]
	     (envs/make-action name #(vector (struct nav-switch-state (map + (:pos %) delta) (:hor? %))
					(if (util/xor (zero? (first delta)) (:hor? %)) +goodmove-reward+ +badmove-reward+))
			  (envs/make-simple-condition #(legal-coord?- (map + (:pos %) delta) height width)))))
      (fn [state]
	(let [coord (:pos state)]
	  (util/lazy-cons-when 
	   (when (contains? switch-coords coord)
	     (envs/make-action 'flip #(vector (struct nav-switch-state (:pos %) (not (:hor? %))) +flip-reward+) 
			  (envs/make-simple-condition #(contains? switch-coords (:pos %)))))
	   (for [[name delta] [['left [-1 0]] ['right [1 0]] ['up [0 -1]] ['down [0 1]]]
		 :when (legal-coord?- (map + coord delta) height width)]
	     (envs/make-action name #(vector (struct nav-switch-state (map + (:pos %) delta) (:hor? %))
					(if (util/xor (zero? (first delta)) (:hor? %)) +goodmove-reward+ +badmove-reward+))
			  (envs/make-simple-condition #(legal-coord?- (map + (:pos %) delta) height width))))))))
     (envs/make-simple-condition #(= (:pos %) goal-pos) true))))

(defn get-nav-switch-heuristic [goal-pos]
  (fn [state]
    (let [pos (util/safe-get state :pos)]
      (- 0 
	 (util/abs (- (first pos) (first goal-pos)))
	 (util/abs (- (second pos) (second goal-pos)))))))

(comment 
  (do (reset-ref-counter) (println (second (a-star-search (ss-node (make-nav-switch-env 4 4 [[1 1]] [0 3] true [3 0]) (get-nav-switch-heuristic [3 0])))) (sref-get *ref-counter*)))

)



(let [f (util/path-local "nav_switch.pddl")]
  (defn make-nav-switch-strips-domain []
    (strips/read-strips-planning-domain f)))
 
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
       (str pos hor?)
	#_(util/str-join "\n"
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


(defn make-random-nav-switch-args [size n-switches]
  (util/assert-is (>= (* size size) n-switches))
  [size size 
   (vec (take n-switches (distinct (repeatedly #(vector (rand-int size) (rand-int size))))))
   [(dec size) 0]
   true
   [0 (dec size)]])

(defn make-random-nav-switch-args-code 
  ([size n-switches] (make-random-nav-switch-args-code size n-switches (rand-int 100000)))
  ([size n-switches seed]
     (util/assert-is (>= (* size size) n-switches))
     [size size 
      `(let [r# (java.util.Random. ~seed)]
	 (vec (take ~n-switches (distinct (repeatedly #(vector (.nextInt r# ~size) (.nextInt r# ~size)))))))
      [(dec size) 0]
      true
      [0 (dec size)]]))

(defn make-random-nav-switch-strips-env [size n-switches]
  (apply make-nav-switch-strips-env (make-random-nav-switch-args size n-switches)))


(defn make-flat-nav-switch-heuristic [env]
  (let [goal (envs/get-goal env)
	pos  (envs/get-positive-conjuncts goal)
	goal-x (util/desymbolize (second (util/make-safe (util/find-first #(= (first %) 'atx) pos))) 1)
	goal-y (util/desymbolize (second (util/make-safe (util/find-first #(= (first %) 'aty) pos))) 1)]
    (util/assert-is (= (count pos) 2))
   (fn [state] 
     (* -2 (+ (util/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) goal-x)) 
	      (util/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) goal-y)))))))





  
  
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
