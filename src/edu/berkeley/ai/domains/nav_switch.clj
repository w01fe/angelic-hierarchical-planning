(ns edu.berkeley.ai.domains.nav-switch
 (:refer-clojure)
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
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
     (states/make-state-set
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

(defn make-nav-switch-strips-domain []
  (strips/make-strips-planning-domain 
   'nav-switch
   [:xc :yc]
   nil
   '[[atx :xc] [aty :yc] [horiz] [above :yc :yc] [left-of :xc :xc] [switch-at :xc :yc]]
   [(strips/make-strips-action-schema 'flip-h '[[:xc x] [:yc y]] '[[atx x] [aty y] [switch-at x y]] '[[horiz]] '[[horiz]] [] (- +flip-reward+))
    (strips/make-strips-action-schema 'flip-v '[[:xc x] [:yc y]] '[[atx x] [aty y] [switch-at x y] [horiz]] [] [] '[[horiz]] (- +flip-reward+))
    (strips/make-strips-action-schema 'good-up [[:yc 'old] [:yc 'new]] '[[aty old] [above new old]] '[[horiz]] '[[aty new]] '[[aty old]] (- +goodmove-reward+))
    (strips/make-strips-action-schema 'bad-up  [[:yc 'old] [:yc 'new]] '[[horiz] [aty old] [above new old]] [] '[[aty new]] '[[aty old]] (- +badmove-reward+))
    (strips/make-strips-action-schema 'good-down [[:yc 'old] [:yc 'new]] '[[aty old] [above old new]] '[[horiz]] '[[aty new]] '[[aty old]] (- +goodmove-reward+))
    (strips/make-strips-action-schema 'bad-down  [[:yc 'old] [:yc 'new]] '[[horiz] [aty old] [above old new]] [] '[[aty new]] '[[aty old]] (- +badmove-reward+))
    (strips/make-strips-action-schema 'good-left [[:xc 'old] [:xc 'new]] '[[horiz] [atx old] [left-of new old]] [] '[[atx new]] '[[atx old]] (- +goodmove-reward+))
    (strips/make-strips-action-schema 'bad-left  [[:xc 'old] [:xc 'new]] '[[atx old] [left-of new old]] '[[horiz]] '[[atx new]] '[[atx old]] (- +badmove-reward+))
    (strips/make-strips-action-schema 'good-right [[:xc 'old] [:xc 'new]] '[[horiz] [atx old] [left-of old new]] [] '[[atx new]] '[[atx old]] (- +goodmove-reward+))
    (strips/make-strips-action-schema 'bad-right  [[:xc 'old] [:xc 'new]] '[[atx old] [left-of old new]] '[[horiz]] '[[atx new]] '[[atx old]] (- +badmove-reward+))]))

(defn make-nav-switch-strips-env [height width switch-coords initial-pos initial-hor? goal-pos]
  (strips/make-strips-planning-instance 
   "nav-switch"
   (make-nav-switch-strips-domain)
   {:xc (map #(util/symbol-cat "x" %) (range width))
    :yc (map #(util/symbol-cat "y" %) (range height))}
   (concat (if initial-hor? '[[horiz]] '[[vert]])
	   [['atx (util/symbol-cat "x" (first initial-pos))] ['aty (util/symbol-cat "y" (second initial-pos))]]
	   (map (fn [pos] ['switch-at (util/symbol-cat "x" (first pos)) (util/symbol-cat "y" (second pos))]) switch-coords)
	   (map (fn [x] ['left-of (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	   (map (fn [x] ['above   (util/symbol-cat "y" (dec x)) (util/symbol-cat "y" x)]) (range 1 height)))
   [['atx (util/symbol-cat "x" (first goal-pos))] ['aty (util/symbol-cat "y" (second goal-pos))]]))
    
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
      (strips/constant-predicate-simplify-strips-planning-instance  
       (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])))))
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/flatten-strips-instance
       (strips/constant-predicate-simplify-strips-planning-instance  
	(make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))))))



  
  
(comment 
  (u util search search.algorithms.textbook domains.nav-switch)
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0) 100 1))
  (map :name (first (a-star-search (state-space-search-node (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0)))))
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) #(reduce + (map (comp (fn [x] (* -2 (Math/abs x))) -) (:pos %) [0 1])) 10 1))

  (dotimes [_ 3] (time (map :name (first (a-star-search (state-space-search-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))))
  ; right now STRIPS is about equal in speed to hand-coded, with new successor generator!
    ; TODO: reachability analysis (planning graph?)
    ; TODO: flatten
    ; TODO: constant substitution

  (time (second (a-star-search (make-initial-state-space-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))
 ; "Elapsed time: 3596.095 msecs"


  )