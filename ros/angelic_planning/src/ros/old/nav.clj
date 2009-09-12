(ns ros.nav
  (:import [java.util HashMap])
  (:use    ;clojure.contrib.test-is 
           ros.ros ros.actions
	   edu.berkeley.ai.domains.nav-2d
	   edu.berkeley.ai.util
	   edu.berkeley.ai.domains.strips
	   edu.berkeley.ai.search
	   edu.berkeley.ai.search.algorithms.textbook
	   edu.berkeley.ai.angelic.hierarchies
	   edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees
	   edu.berkeley.ai.angelic.hierarchies.offline-algorithms
	  ))
  

;  (:require [edu.berkeley.ai.util :as util] ))


(import-ros)

(set! *warn-on-reflection* true)

(defmsgs [ros.pkg.roslib.msg Header]
         [ros.pkg.std_msgs.msg ColorRGBA]
	 [ros.pkg.robot_msgs.msg OccGrid MapMetaData Point Pose 
	   PoseDot PoseDDot Velocity AngularVelocity Acceleration AngularAcceleration 
	   PoseStamped PoseWithRatesStamped Quaternion]
	 [ros.pkg.nav_robot_actions.msg MoveBaseState]
	 [ros.pkg.topological_map.msg Cell Connector ConnectorEdge MapRegion]
	 [ros.pkg.visualization_msgs.msg Polyline])

(defsrvs [ros.pkg.robot_srvs.srv StaticMap]
         [ros.pkg.topological_map.srv GetTopologicalMap])




; ./map_server ../../demos/2dnav_stage/maps/willow-full-0.025.pgm 0.025

(defonce *map* nil)
(defonce *inflated-map* nil)
(defonce *map-free-fn*  nil)
(defonce *current-pose* (atom nil))

(defonce *map-res* nil)
(defonce *map-dims* nil)
(defonce *map-scale* nil)
(defonce *radius* nil)
(defonce *regions* nil)

(defn cont->disc [[x y]]
  [(int (/ (double x) (double *map-res*)))
   (int (/ (double y) (double *map-res*)))])

(defn disc->cont [[x y]]
  [(* (+ (double x) 0.5) (double *map-res*))
   (* (+ (double y) 0.5) (double *map-res*))])


(defn point->disc-pos [point]
  (cont->disc [(:x point) (:y point)]))

(defn point->cont [point] [(:x point) (:y point)])

(defn disc-pos->point [pair]
  (let [[x y] (disc->cont pair)]
    {:class Point :x x :y y :z 0.0}))

(defn pose->disc-pos [pose] (point->disc-pos (:position pose)))


(defn flood-fill [#^"[Z" m w x y]
  (let [w (int w)]
  (loop [s (list [x y]) c 0]
    (if s
      (let [[x y] (first s) x (int x) y (int y)]
        (if (aget m (+ x (* w y)))
            (recur (next s) c)
	  (do (aset-boolean m (+ x (* w y)) true)
	      (recur (concat (for [[dx dy] [[-1 0] [1 0] [0 -1] [0 1]]] [(+ x dx) (+ y dy)]) (next s))
		     (inc c)))))
      
      c))))

(defn fill-small-regions [width height #^"[Z" fill-map thresh]
  (let [width (int width) height (int height) thresh (int thresh)
	#^"[Z" m     (java.util.Arrays/copyOf fill-map (* width height))]
    (doseq [y (range height), x (range width)]
      (when (and (not (aget m (int (+ x (* y width)))))
		 (< (flood-fill m width x y) thresh))
;	(println "Filling" x y)
	(flood-fill fill-map width x y)))))

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
    (def *inflated-map* fill-map)
    (doseq [y (range height), x (range width)]
      (let [x (int x) y (int y)]
	(when-not (free-fn [x y])
	  (aset-boolean fill-map (+ x (* y width)) true)
	  (when (some (fn [[dx dy]]
			(let [dx (int dx) dy (int dy)
			      nx (+ x dx), ny (+ y dy)]
			  (and (>= nx 0) (< nx width) (>= ny 0) (< ny height) (free-fn [nx ny]))))
		      [[-1 0] [1 0] [0 -1] [0 1]])
	    (doseq [[dx dy] offsets]
	      (let [dx (int dx), dy (int dy),
		    nx (+ x dx), ny (+ y dy)]
		(when (and (>= nx 0) (< nx width) (>= ny 0) (< ny height))
		  (aset-boolean fill-map (+ nx (* ny width)) true))))))))
    (fill-small-regions width height fill-map 10000)
    (fn [[x y]]
      (let [x (int x) y (int y)]
	(not (aget fill-map (+ x (* y width))))))
#_    (fn [[x y]]
      (let [x (int x) y (int y)]
	(cond (not (aget fill-map (+ x (* y width)))) 
	        :free
	      (some (fn [[dx dy]]
		      (let [dx (int dx) dy (int dy)
			    nx (+ x dx), ny (+ y dy)]
			(and (>= nx 0) (< nx width) (>= ny 0) (< ny height) 
			     (not (aget fill-map (+ nx (* ny width)))))))
		    [[-1 0] [1 0] [0 -1] [0 1]])
	        :border
	      :else 
                :occupied)))))


#_
(defn make-map-update-callback []
  (let [w (int (first *map-dims*)) h (int (second *map-dims*))
	#^"[Z" fill-map *inflated-map*   res (double *map-res*)]
    (make-subscriber-callback 
     (fn [m]
       (let [#^Polyline m m]
	 (doseq [#^Point p (.points m)]
	   (aset-boolean fill-map (+ (int (/ (.x p) res)) (* w (int (/ (.y p) res)))) true)))))))
	    

(defn visualize-local-map [r]
  (put-message "/angelic/localmap"
    (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
	      :color {:class ColorRGBA :r 1.0 :g 1.0 :b 0.0 :a 0.0} 
	      :points 
      (let [w (int (first *map-dims*))  h (int (second *map-dims*)) 
	     #^"[Z" fill-map *inflated-map*
	     #^"[B" regions *regions*
	    [x y] (pose->disc-pos @*current-pose*)
	    reg (aget regions (int (+ x (* w y))))]
	(for [dy (range (- (min r y)) (min (- h y) (inc r))) dx (range (- (min r x)) (min (- w x) (inc r)))
	      :let [c (int (+ x dx (* w (+ y dy))))]
	      :when (and (aget fill-map c) #_ (= reg (aget regions c))) ] 
	  (disc-pos->point [(+ x dx) (+ y dy)])))})))

(defn make-map-update-callback []
  (make-subscriber-callback 
     (fn [m]
       (let [w (int (first *map-dims*)) h (int (second *map-dims*))
	     #^"[Z" fill-map *inflated-map*   res (double *map-res*) scale *map-scale*
	     counter (HashMap.)
	     #^Polyline m m]
	 (doseq [#^Point p (.points m)]
	   (let [xy (+ (int (/ (.x p) res)) (* w (int (/ (.y p) res))))]
	     (.put counter xy (+ 1 (or (.get counter xy) 0)))))
	 (doseq [[ind cnt] counter]
	   (when (= cnt (* scale scale))
	    ; (print [(mod ind w) (int (/ ind w))])
	     (aset-boolean fill-map ind true ))))
       (visualize-local-map 40))))



(defn downscale-map [#^java.util.ArrayList data scale old-w new-w new-h]
  (let [new-w (int new-w) new-h (int new-h) old-w (int old-w) scale (int scale)
	ret (java.util.ArrayList. (* new-w new-h))]
    (doseq [y (range new-h), x (range new-w)]
      (.add ret (if (some #(not (zero? %)) 
			  (for [dy (range scale), dx (range scale)]
			    (.get data (+ (* scale x) dx (* old-w (+ (* scale y) dy))))))
		  1 0)))
    ret))

(defn get-map 
  ([] (get-map 1))
  ([downscale]
  (with-node-handle [nh]
    (let [static-map->msg
	    (.call (.serviceClient nh "static_map" (StaticMap.) false)
		   (StaticMap$Request.))
	  {:keys [#^java.util.ArrayList data info]} (:map (time (msg->map static-map->msg)))
	  w (int (/ (:width info) downscale)) h (int (/ (:height info) downscale))
	  #^java.util.ArrayList data (if (> downscale 1) 
				       (downscale-map data downscale (:width info) w h) data)]
      (doseq [x (range w)] 
	(.set data x 255)
	(.set data (+ x (* (dec h) w)) 255))
      (doseq [y (range h)] 
	(.set data (* w y) 255)
	(.set data (+ (dec w) (* y w)) 255))
	
      (def *map* data)
      (def *map-res* (* downscale (:resolution info)))
      (def *map-scale* downscale)
      (def *map-dims* [w h] )
      (def *radius* (int (/ (- 0.325 #_(.getDoubleParam nh "/move_base/base_local_planner/inflation_radius") 0.025) *map-res*)))
      (def *pre-map* (time (preprocess-map w h (fn [[x y]] (zero? (.get data (+ (int x) (* (int y) w))))) *radius*)))
      ))))

;      (def *dom* chy* (constant-predicate-simplify (make-nav-2d-strips-env *pre-map* [w h] [450 350] [460 350])))))

; 

; (time )

; (time (solution-name (aha-star-search (alt-node *h*))))



(defonce *topo-map* nil)
(defn get-topo-map []
  (def *topo-map* (call-service "topological_map" (GetTopologicalMap$Request.))))

(defn region-points [reg]
  (let [pc #(vector (/ (:x %) *map-scale*) (/ (:y %) *map-scale*))
	cells (map pc (:cells reg))
	;cells (or (seq (filter (fn [[x y]] (zero? (mod y 3))) cells)) cells)
	]
    (loop [points (concat [[9000 9000]] cells [(first cells) [(ffirst cells) (- (second (first cells)) 10)] [8000 8000]]) res []]
      (if (not (nthnext points 2)) res
        (let [pp (first points)
	      cp (second points)
	      np (nth points 2)]
	  (if (= (second pp) (second cp) (second np)) (recur (next points) res)
	    (recur (next points) (conj res cp))))))))

(defn visualize-regions []
  (put-message "/angelic/regions" 
    (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
	      :color {:class ColorRGBA :r 1.0 :g 0.0 :b 0.0 :a 0.0} 
	      :points 
      (doall (apply concat
        (for [reg (filter #(<= 1000 (count (:cells %))) (:regions *topo-map*))
	      :let   [pts (region-points reg)]]
	  (map disc-pos->point (apply concat (partition 2 1 pts))))))})))

(defn visualize-regions-animate []
  (doseq [reg (partition 5 (shuffle (filter #(<= 1000 (count (:cells %))) (:regions *topo-map*))))
	  :let   [regs (map region-points reg)]]
    (Thread/sleep 2.0)
    (put-message "/angelic/regions"
       (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
		 :color {:class ColorRGBA :r 1.0 :g 0.0 :b 0.0 :a 0.0} 
		 :points 
         (mapcat (fn [pts] (map disc-pos->point (apply concat (partition 2 1 pts)))) regs)}))))

(def *search-pattern* 
     (cons [0 0]
      (apply concat 
       (for [i (range 1 1000),
	     j (range (- i) i)]
	 [[j     (- i (Math/abs (int j)))]
	  [(- j) (- (Math/abs (int j)) i)]]))))

(defonce *regions* nil)


(defn build-topo-regions []
  (let [w (int (first *map-dims*))
	h (int (second *map-dims*))
	scale (int *map-scale*)
	points-by-region (HashMap.)
	#^"[Z" static-map    *inflated-map* 
;	#^"[B" given-regions (make-array Byte/TYPE (* w h))
	#^"[B" regions       (make-array Byte/TYPE (* w h))]
    (time 
    (doseq [[id rgn] (indexed (filter #(<= 1000 (count (:cells %))) (:regions *topo-map*))),
	    [x y]    (map #(vector (/ (:x %) scale) (/ (:y %) scale)) (:cells rgn))]
      (let [x (int x) y (int y) c (int (+ (int x) (* w (int y))))]
	(when-not (aget static-map c)
	  (aset-byte regions c (byte (inc id)))
	  (.put points-by-region (inc id) (conj (or (.get points-by-region (inc id)) []) [x y]))))))
    (time
     (loop [frontiers points-by-region]
;       (println (map count (vals frontiers)))
       (when (seq frontiers)
	 (recur
	  (into {}
	    (for [[reg pts] frontiers
		  :let [next-pts
			(for [[x y]   pts
			      [dx dy] [[-1 0] [1 0] [0 -1] [0 1]]
			      :let [nx (+ (int x) (int dx))
				    ny (+ (int y) (int dy))
				    c  (+ nx (* w ny))]
			      :when (and (= (byte 0) (aget regions c))
					 (not (aget static-map c)))]
			  (do (aset-byte regions c (byte reg))
			      (.put points-by-region reg (conj (.get points-by-region reg) [nx ny]))
			      [nx ny]))]			  
		  :when (seq (doall next-pts))]
	      [reg next-pts]))))))
    #_
    (doseq [y (range h) x (range w)]
      (let [x (int x) y (int y) c (int (+ x (* w y)))]
	(when (not (aget static-map (int c)))
	  (let [reg (byte 
			(some (fn [[dx dy]]
				(let [dx (int dx) dy (int dy) nx (+ x dx) ny (+ y dy)
				      nc (+ nx (* w ny))]
				  (when (and (>= nx 0) (< nx w) (>= ny 0) (< ny h))
				    (let [v (byte (aget given-regions nc))]
				      (when (> (int v) (int 0)) v)))))
			      *search-pattern*))]
	    (aset-byte regions c reg)
	    (.put points-by-region reg (conj (or (.get points-by-region reg) []) [x y]))
	    ))))
    (def *regions* regions)
    (def *points-by-region* points-by-region)))




(defn visualize-my-regions []
  (let [#^HashMap points-by-region *points-by-region*]
    (doseq [reg (partition-all 5 (shuffle  (vals points-by-region) 
				        #_ (map #(.get points-by-region (byte %)) [12] #_ [2 41 10 15])))]
      (Thread/sleep 2000.0)
      (put-message "/angelic/regions"
       (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
		 :color {:class ColorRGBA :r 1.0 :g 0.0 :b 0.0 :a 0.0} 
		 :points 
         (apply concat (map (fn [pts] (map disc-pos->point pts)) reg))})))))


(defonce *connectors* nil)

(defn cluster-connectors 
  "Split connectors into partitions based on proximity"
  [connectors]
  (let [extract-cluster 
	  (fn [cluster other-connectors]
	    (let [[good-pts bad-pts]
		  (separate (fn [[[x1 y1]]] 
			    (some (fn [[[x2 y2]]]
				    (and (<= (abs (- x1 x2)) 2) (<= (abs (- y1 y2)) 2)))
				  cluster))
			  other-connectors)]
	      (if (seq good-pts)
		  (recur (concat cluster good-pts) bad-pts)
		[cluster other-connectors])))]
    (loop [clusters [] connectors (seq connectors)]
      (if (empty? connectors) clusters
	(let [[cluster other-connectors] (extract-cluster [(first connectors)] (next connectors))]
	  (recur (conj clusters cluster) other-connectors))))))

(defn pick-best-connector [cluster]
  (let [w (int (first *map-dims*))
	#^"[Z" static-map    *inflated-map*]
  (first 
   (sort-by 
    (fn [pts]
      (- (apply + 
       (for [[x y] pts]
	 (first 
	  (filter (fn [dist] 
		    (some (fn [dy] (some (fn [dx]
					  (and (< (+ (* dx dx) (* dy dy)) (* dist dist))
					       (aget static-map (int (+ x dx (* (+ y dy) w))))))
					 (range (- dist) (inc dist))))
			  (range (- dist) (inc dist))))
		  (iterate inc 0)))))))
    cluster))))
	 
	


(defn find-topo-connectors [] 
  (let [w (int (first *map-dims*))
	h (int (second *map-dims*))
	#^"[B" regions  *regions*
	connectors (HashMap.)
	connector-targets (HashMap.)
	region-connectors (HashMap.)]
    (doseq [y (range h) x (range w)]
      (let [x (int x) y (int y) c (int (+ x (* w y)))
	    r (int (aget regions (int c)))]
	(when (> r (int 0))
	  (let [lr (int (aget regions (int (dec c))))
		ur (int (aget regions (int (- c w))))]
	    (cond (and (> lr (int 0)) (not (= lr r)))
		    (let [[so pr] (if (< r lr)
				    [[r lr] [[x y] [(dec x) y]]]
				    [[lr r] [[(dec x) y] [x y]]])]
		      (.put connectors so (cons pr (.get connectors so))))
		  (and (> ur (int 0)) (not (= ur r)))
		    (let [[so pr] (if (< r ur)
				    [[r ur] [[x y] [x (dec y)]]]
				    [[ur r] [[x (dec y)] [x y]]])]
		      (.put connectors so (cons pr (.get connectors so)))))))))
    (doseq [[[r1 r2] conns] connectors
	    cluster         (cluster-connectors conns)]
      (let [[p1 p2] (pick-best-connector cluster)]
	(.put region-connectors (int r1) (cons p1 (.get region-connectors (int r1))))
	(.put region-connectors (int r2) (cons p2 (.get region-connectors (int r2))))
	(.put connector-targets p1 p2)
	(.put connector-targets p2 p1)))
    
    (def *connectors* connectors)
    (def *connector-targets* (into {} connector-targets))
    (def *region-connectors* (into {} region-connectors))))




(defn visualize-my-connectors []
  (put-message "/angelic/regions"
       (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
		 :color {:class ColorRGBA :r 1.0 :g 0.0 :b 0.0 :a 0.0} 
		 :points 
	 (map disc-pos->point 
	      (mapcat (fn [c] [c (*connector-targets* c)])
		      (apply concat (vals *region-connectors*))))})))


(defn primitive-plan-points [init-point plan]
  (lazy-seq 
    (cons init-point 
      (when-let [a (first plan)]
	(primitive-plan-points 
	 (if (= (:name a) 'connect) 
	     (safe-get* *connector-targets* init-point)
	   (vec (map + init-point (safe-get* *nav-actions* (:name a)))))
	 (next plan))))))

(defn next-primitive-plan-point [init-point a]
  (if (= (:name a) 'connect) 
    (safe-get* *connector-targets* init-point)
    (vec (map + init-point (safe-get* *nav-actions* (:name a))))))


(defn connect-topo-connectors [] 
  (let [w (int (first *map-dims*))
	region-connectors *region-connectors*
	#^"[B" regions              *regions*
	#^"[Z" static-map           *inflated-map*
	connector-distances         (HashMap.)]  ; map from points to [pt rew]
    ; Distances are actually rewards.
    (def *path-points*
    (apply concat 
    (doall 
    (for [[r conns] region-connectors
          [src dst] (combinations conns 2)]
      (let [[sol rew] 
	    (a-star-graph-search 
	     (ss-node 
	      (make-nav-2d-env (fn [[x y]] 
				 (and (= r (aget regions (int (+ x (* w y)))))
				      (*pre-map* [x y])))
			       *map-dims* src dst)
	      (make-nav-2d-heuristic dst)))]
	(print ".")
	(.put connector-distances src (cons [dst rew] (get connector-distances src)))
	(.put connector-distances dst (cons [src rew] (get connector-distances dst)))
	(map disc-pos->point (apply concat (partition 2 1 (primitive-plan-points src sol)))))))))
    
    (def *connector-distances* (into {} connector-distances))))



(defn visualize-connector-plans []
    (put-message "/angelic/regions" 
     (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
	       :color {:class ColorRGBA :r 1 :g 0.5 :b 0.26 :a 0.0} 
	       :points *path-points*})))


(defn get-topo-distances []
  (if (.exists (java.io.File. "/tmp/dists.txt"))
      (def *connector-distances* (read-string (slurp "/tmp/dists.txt")))
    (do (connect-topo-connectors)
	(spit "/tmp/dists.txt" *connector-distances*))))

(defn build-topo-map [] (get-topo-map) (build-topo-regions) (find-topo-connectors) (get-topo-distances)); #_(connect-topo-connectors))



; *connector-distances*


; (interactive-search (alt-node (make-nav-regions-hierarchy (make-nav-regions-env (fn [[x y]] (int (aget *regions* (int (+ x (* (first *map-dims*) y)))))) *region-connectors* *connector-targets* *connector-distances* [191 291] [189 231]))))




(defn move-to-point [point]
  (with-node-handle [nh]
    (run-action nh "/move_base" 
      (map->msg {:class PoseStamped :header {:class Header :frame_id "/map"} 
		:pose {:class Pose :position (disc-pos->point point) 
		       :orientation {:class Quaternion :x 0 :y 0 :z 0 :w 1.00}}})
      (MoveBaseState.))))

(defn dist [[x1 y1] [x2 y2]]
  (let [dx (- x2 x1) dy (- y2 y1)]
    (Math/sqrt (double (+ (* dx dx) (* dy dy))))))

(defn plan-obstructed? [points]
  (let [w (int (first *map-dims*)) h (int (second *map-dims*))
	#^"[Z" fill-map *inflated-map*   res (double *map-res*)]
    (find-first (fn [[x y]] 
		  (let [c (int (+ x (* w y)))]
		    (and ;(= reg (int (aget regions c))) 
		     (aget fill-map (int (+ x (* w y)))))))
		points)))

(defn angle->orientation [rads]
  {:class Quaternion :x 0 :y 0 :z (Math/sin (double (/ rads 2))) 
   :w (Math/cos (double (/ rads 2)))})

(defn approx-= [x y] (let [x (double x) y (double y)] (< (Math/abs (- x y)) 0.0000000001)))

(defn orientation->angle [orientation]
  (assert (and (zero? (:x orientation)) (zero? (:y orientation))))
  (let [r (* 2 (Math/atan2 (double (:z orientation)) (double (:w orientation))))]
    (if (< r 0) (+ r (* Math/PI 2)) r)))

(defn vector->angle [[x y]]
  (Math/atan2 (double y) (double x)))

(def *plan-agent* (agent [[] []]))

(declare make-and-execute-plan)
(defn execute-plan [dest dst-orientation horizon interval]
  (let [w (int (first *map-dims*))
	#^"[B" regions  *regions* #^"[Z" fill-map *inflated-map*
	dur    (Duration. (double interval))]
  (with-node-handle [nh]
    (loop [tries 50 pi 0 #^Time t (.add (.now nh) dur) hor horizon ]
 ;     (println tries pi t (.now nh) (.hasElapsed t dur)) (Thread/sleep 10)
      (.spinOnce nh)
      (let [pos (pose->disc-pos  @*current-pose*) 
	    points (first @*plan-agent*)]
	(cond (<= tries 0) false
	      (<= (dist pos dest) 2) true
	      (and (< (inc pi) (count points)) (< (dist (points pi) pos) hor)
		   (not (aget fill-map (int (+ (first (points (inc pi))) (* w (second (points (inc pi)))))))))
	        (recur 50 (inc pi) t hor)
	      (not (.hasElapsed t dur))
	        (if-let [[ox oy] (plan-obstructed? (subvec points (max 0 (- pi horizon)) (min (count points) (+ pi 50))))]
	           (if (= (int (aget regions (int (+ (first pos) (* w (second pos))))))
			  (int (aget regions (int (+ ox (* w oy))))))
		       (do 
			 (println "plan obstructed at " ox oy "; replanning")
			 (make-and-execute-plan dest dst-orientation)
			 )
;		     (recur tries (- pi (int (/ hor 1.4))) t (dec (int (dist [ox oy] pos)))))
		     (recur tries pi t hor))
		 (recur tries pi t hor))
	      :else
	  (do ;(println pos points) 
	      (println pi hor)
;	      (visualize-path (take 10 points))
	      (put-message "/move_base/activate"
	        (map->msg {:class PoseStamped :header {:class Header :frame_id "/map"} 
			  :pose {:class Pose :position (disc-pos->point (points pi)) 
				 :orientation (if (>= pi (- (count points) 5)) 
						  dst-orientation
						(angle->orientation
						 (vector->angle 
						  (map - (points (+ 4 pi)) (points pi)))))}}))
	      (recur (dec tries) pi (.now nh) hor))))))))
(comment
(put-message "/move_base/activate"
	        (map->msg {:class PoseStamped :header {:class Header :frame_id "/map"} 
			  :pose {:class Pose :position {:class Point :x 15.2194343567
    :y 5.506299636841
    :z 0.0}
#_(disc-pos->point [625 438]) 
				 :orientation (angle->orientation 0)}}))
)
(defn visualize-path [points]
  (put-message "/angelic/traverse" 
    (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
	      :color {:class ColorRGBA :r 1 :g 0.5 :b 0.26 :a 0.0} 
	      :points (map disc-pos->point [[0 0]])}))
  (put-message "/angelic/plan" 
    (map->msg {:class Polyline :header {:class Header :frame_id "map"} 
	      :color {:class ColorRGBA :r 1 :g 0.5 :b 0.26 :a 0.0} 
	      :points (map disc-pos->point (apply concat (partition 2 1 points)))})))


(import '[java.util ArrayList])

(defn visualize-high-level-solution [src hlas]
  (let [prim (ArrayList.)
	connect (ArrayList.)
	traverse (ArrayList.)]
;    (println (map hla-name hlas))
    (loop [src src hlas hlas]
      (when-first [hla hlas]
	(if (or (= (hla-name hla) '[finish]) (= (hla-name hla) '[noop]))
	  (recur src (next hlas))
;	(when-not (= (hla-name hla) '[finish])
	(if (hla-primitive? hla)
	  (let [a (hla-primitive hla)]
;	    (println (:name a))
	    (if (= (:name a) 'connect)
	        (let [dst (safe-get* *connector-targets* src)]
	  	  (.add connect src)
		  (.add connect dst)
		  (recur dst (rest hlas)))
	      (let [dst (vec (map + src (safe-get* *nav-actions* (:name a))))]
		(.add prim src) (.add prim dst)
		(recur dst (rest hlas)))))
	  (let [[n sp dp] (hla-name hla)]
	    (assert (= n 'traverse))
	    (assert (= sp src))
	    (.add traverse sp) (.add traverse dp)
	    (recur dp (rest hlas)))))))
    (doseq [[topic color pts]
	    [["/angelic/plan" {:class ColorRGBA :r 1 :g 0.5 :b 0.26 :a 0.0} (concat prim connect)]
	     ["/angelic/traverse" {:class ColorRGBA :r 0.0 :g 0.0 :b 1.0 :a 0.0} traverse]]]
      (put-message topic 
	(map->msg {:class Polyline :header {:class Header :frame_id "map"} 
		  :color color 
		  :points (map disc-pos->point pts)})))))

(defn next-step [[points next-node]]
  (if (isa? (:class next-node) :edu.berkeley.ai.search/Node)
      (let [nds (next (reverse (iterate-while :previous (:plan next-node))))
	    acts (map :hla nds)
	    prims (map hla-primitive (take-while hla-primitive? acts))
	    pts   (vec (primitive-plan-points (first points) prims))
	    next-node (reroot-at-node next-node)]
	(visualize-high-level-solution (first points) acts)
	[pts next-node])			     
    (let [pts (vec (primitive-plan-points (first points) (first next-node)))]
      (visualize-path pts)
      [pts nil])))


(defn refine-step [[points node]] 
  (if node
      (let [out (next-step [points (ahss-et-search node (lower-reward-bound node))])]
	(send *plan-agent* refine-step)
	out)
    [points node]))


; TODO: may still fail if we have to leave then traverse through region.
(defn make-and-execute-plan [dst dst-orientation]
  (send *plan-agent* (constantly [[] nil]))
  (await *plan-agent*)
;  (dosync (ref-set *prim-prefix* []) (ref-set *rest-plan* []))
  (let [src (pose->disc-pos @*current-pose*)
	_   (println src dst)
	w (int (first *map-dims*))
	#^"[B" regions  *regions*
	init-region (int (aget regions (int (+ (first src) (* w (second src))))))
	#^"[Z" fill-map *inflated-map* 
	e   (time (make-nav-regions-env 
		   (memoize ;; Prevent map from changing out from under.
		   (fn [[x y]]
		     (let [c (int (+ x (* w y)))
			   reg (int (aget regions c))]
		       (if (and (= reg init-region) (aget fill-map c)) 0 reg))))
		   *region-connectors* *connector-targets* *connector-distances*
		   src dst))
	sol    (time (aha-star-et-search (alt-node (make-nav-regions-hierarchy e) 
					     {:graph? :full :ref-choice-fn first-gap-choice-fn})))]
    (if (not sol)
        (do (println "Failed to find solution; clearing map and retrying.")
	    (get-map *map-scale*)
	    (recur dst dst-orientation))
      (do 
	(send *plan-agent* (constantly (next-step [[src] sol])))
	(await *plan-agent*)
	(send *plan-agent* refine-step)
	(println (execute-plan dst dst-orientation 20 1))))))
;      (let [;_ (println (class sol) (:class sol))
;	    pts (primitive-plan-points src sol)] ;(seque 50 (streaming-search sol)))]
;        (visualize-path pts)
;	  (println pts)
;	(println (execute-plan dst dst-orientation 20 1))
;))))


(defn wait-for-goals 
  ([] (wait-for-goals 1))
  ([n]
   (with-node-handle [nh]
     (reset! *current-pose* nil)
     (let [g (atom nil)
	   s3 (.subscribe nh "/base_pose_ground_truth" (PoseWithRatesStamped.)
			  (sub-cb [m] (reset! *current-pose* (:pos m)))  1)
	   _ (while (not @*current-pose*) (.spinOnce nh))
	   s (.subscribe nh "/angelic/nav/activate" (PoseStamped.)
			   (sub-cb PoseStamped [m] (reset! g m)) 1)
	   s2 (.subscribe nh "/move_base/local_costmap/inflated_obstacles"
			  (Polyline.) (make-map-update-callback) 1)

	   ]
       (loop [n n]
	 (when (> n 0)
	   (while (not @g) (.spinOnce nh))
	   (make-and-execute-plan (pose->disc-pos (:pose @g)) (:orientation (:pose @g)))
	   (reset! g nil)
	   (recur (dec n))))))))


    
  

;(put-message "/angelic/plan" (map->msg {:class ros.pkg.visualization_msgs.msg.Polyline :header {:class ros.pkg.roslib.msg.Header :frame_id "map"} :color {:class ros.pkg.std_msgs.msg.ColorRGBA :r 1 :g 0.5 :b 0.26 :a 0.0} :points (map disc-pos->point [[100 100] [900 900] [100 900] [100 100] [600 200] [300 800]])}))

;  (with-node-handle [nh] (when-let [ac (make-action-client nh "/move_base" (PoseStamped.) (MoveBaseState.))] (println "got action client!") (execute-action-client ac (map->msg {:class PoseStamped :header {:class Header :frame_id "map"} :pose {:class Pose :position {:class Point :x 30.25 :y 17.06 :z 0} :orientation {:class Quaternion :x 0 :y 0 :z 0 :w 1.00}}}) (Duration. 15.0))))




	    
(set! *warn-on-reflection* false)










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
		 [[-1 0] [1 0] [0 -1] [0 1]])))))))



(comment 
  
(defn wait-for-goals 
  ([] (wait-for-goals 1))
  ([n]
   (with-node-handle [nh]
     (let [e (time (constant-predicate-simplify 
		    (make-nav-2d-strips-env *pre-map* *map-dims* 
					    (pose->disc-pos (get-current-pose)) 
					    (pose->disc-pos (get-current-pose)))))
	   g (atom nil)
	   s (.subscribe nh "/angelic/nav/activate" (PoseStamped.)
			   (sub-cb PoseStamped [m] (reset! g m)) 1)]
       (loop [n n]
	 (when (> n 0)
	   (while (not @g) (.spinOnce nh))
	   (let [src (pose->disc-pos (get-current-pose))
		 dst (pose->disc-pos (:pose @g))
		 _   (println dst)
		 e   (time (repurpose-nav-2d-strips-env e src dst))
		 h   (time (get-hierarchy *nav-2d-hierarchy* e))
		 sol (time (first (aha-star-search (alt-node h))))
		 pts (primitive-plan-points src sol)]
	     (visualize-path pts)
;	     (move-to-point (last pts))
	     (reset! g nil)
	     (recur (dec n))))))))))



	  
;	      (println (run-action nh "/move_base"
;	        (map->msg {:class PoseStamped :header {:class Header :frame_id "/map"} 
;			  :pose {:class Pose :position (disc-pos->point (first points)) 
;				 :orientation {:class Quaternion :x 0 :y 0 :z 0 :w 1.00}}})
;		(MoveBaseState.) (Duration. 3.0)))
;		 (> (
;    (let [ac (make-action-client nh "/move_base" (PoseStamped.) (MoveBaseState.))
;	  result
;	   (loop [points points]
;	     (let [err (move-to-point (first points))]
;	       (if (not (= err :success)) err
;		 (when (next points)
;		   (recur (or (drop granularity points) [(last points)]))))))]
;      (shutdown-action-client ac)
;      (or result :success))))

