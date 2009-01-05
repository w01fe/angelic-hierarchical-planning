(ns edu.berkeley.ai.domains.nav-switch
 (:refer-clojure)
 (:use clojure.contrib.str-utils [edu.berkeley.ai.util :as util] edu.berkeley.ai.envs edu.berkeley.ai.envs.states edu.berkeley.ai.domains.strips)
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

(defn make-nav-switch-strips-domain []
  (make-strips-planning-domain 
   "nav-switch"
   [:xc :yc]
   nil
   '[[atx :xc] [aty :yc] [horiz] [vert] [above :yc :yc] [left-of :xc :xc] [switch-at :xc :yc]]
   [(make-strips-action-schema 'flip-h '[[:xc x] [:yc y]] '[[atx x] [aty y] [switch-at x y] [vert]] '[[horiz]] '[[vert]] 1)
    (make-strips-action-schema 'flip-v '[[:xc x] [:yc y]] '[[atx x] [aty y] [switch-at x y] [horiz]] '[[vert]] '[[horiz]] 1)
    (make-strips-action-schema 'good-up [[:yc 'old] [:yc 'new]] '[[vert]  [aty old] [above new old]] '[[aty new]] '[[aty old]] 2)
    (make-strips-action-schema 'bad-up  [[:yc 'old] [:yc 'new]] '[[horiz] [aty old] [above new old]] '[[aty new]] '[[aty old]] 4)
    (make-strips-action-schema 'good-down [[:yc 'old] [:yc 'new]] '[[vert]  [aty old] [above old new]] '[[aty new]] '[[aty old]] 2)
    (make-strips-action-schema 'bad-down  [[:yc 'old] [:yc 'new]] '[[horiz] [aty old] [above old new]] '[[aty new]] '[[aty old]] 4)
    (make-strips-action-schema 'good-left [[:xc 'old] [:xc 'new]] '[[horiz] [atx old] [left-of new old]] '[[atx new]] '[[atx old]] 2)
    (make-strips-action-schema 'bad-left  [[:xc 'old] [:xc 'new]] '[[vert]  [atx old] [left-of new old]] '[[atx new]] '[[atx old]] 4)
    (make-strips-action-schema 'good-right [[:xc 'old] [:xc 'new]] '[[horiz] [atx old] [left-of old new]] '[[atx new]] '[[atx old]] 2)
    (make-strips-action-schema 'bad-right  [[:xc 'old] [:xc 'new]] '[[vert]  [atx old] [left-of old new]] '[[atx new]] '[[atx old]] 4)]))

(defn make-nav-switch-strips-env [height width switch-coords initial-pos initial-hor? goal-pos]
  (make-strips-planning-instance 
   "nav-switch"
   (make-nav-switch-strips-domain)
   {:xc (map #(keyword (str "x" %)) (range width))
    :yc (map #(keyword (str "y" %)) (range height))}
   (concat (if initial-hor? '[[horiz]] '[[vert]])
	   [['atx (keyword (str "x" (first initial-pos)))] ['aty (keyword (str "y" (second initial-pos)))]]
	   (map (fn [pos] ['switch-at (keyword (str "x" (first pos))) (keyword (str "y" (second pos)))]) switch-coords)
	   (map (fn [x] ['left-of (keyword (str "x" (dec x))) (keyword (str "x" x))]) (range 1 width))
	   (map (fn [x] ['above   (keyword (str "y" (dec x))) (keyword (str "y" x))]) (range 1 height)))
   [['atx (keyword (str "x" (first goal-pos)))] ['aty (keyword (str "y" (second goal-pos)))]]))
    


(comment 
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0) 100 1))
  (map :name (first (a-star-search (state-space-search-node (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0)))))
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) #(reduce + (map (comp (fn [x] (* -2 (Math/abs x))) -) (:pos %) [0 1])) 10 1))
  )