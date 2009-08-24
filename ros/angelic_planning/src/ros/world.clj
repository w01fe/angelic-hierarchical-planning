;///////////////////////////////////////////////////////////////////////////////
;// High-level world "simulator" for high-level planning.
;//
;// Copyright (C) 2009, Jason Wolfe
;//
;// Redistribution and use in source and binary forms, with or without
;// modification, are permitted provided that the following conditions are met:
;//   * Redistributions of source code must retain the above copyright notice,
;//     this list of conditions and the following disclaimer.
;//   * Redistributions in binary form must reproduce the above copyright
;//     notice, this list of conditions and the following disclaimer in the
;//     documentation and/or other materials provided with the distribution.
;//   * Neither the name of Stanford University nor the names of its
;//     contributors may be used to endorse or promote products derived from
;//     this software without specific prior written permission.
;//
;// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
;// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;// POSSIBILITY OF SUCH DAMAGE.
;//////////////////////////////////////////////////////////////////////////////



(ns ros.world
  (:use   ros.ros ros.geometry)
	  )
  
(set! *warn-on-reflection* true)

(import-ros)

(defmsgs [mapping_msgs CollisionMap])

(defsrvs [navfn SetCostmap])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Method defs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmulti render-boundary-points (fn [obj res] (:class obj)))


(defstruct costmap :minx :miny :res :width :height :data :dx :dy) 
; all are integers, data is bytes, dx and dy are double offsets from nearest grid point.

; hard-rad and sort-rad are integers.
(defmulti render-2d-costmap (fn [obj res hard-rad soft-rad] (:class obj)))



(defn print-2d-costmap [costmap]
  (let [#^bytes arr (:data costmap)
	width (int (:width costmap))]
    (println
    (apply str 
     (map #(apply str (concat % ["\n"]))
      (partition width
       (map #(let [s (str "     " %)] (.substring s (- (count s) 4))) arr)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Rendered  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmethod render-boundary-points :rendered [obj res] 
  (assert (= res (:3d-res obj))) 
  (:3d-points obj))

(defmethod render-2d-costmap      :rendered [obj res hard-rad soft-rad] 
  (assert (= [res hard-rad soft-rad] (map obj [:2d-res :2d-hard-rad :2d-soft-rad])))
  (:2d-costmap obj))


(defn render-object [obj res3 res2 inflate-hard inflate-soft]
  {:class :rendered :name (:name obj) :xyz [0 0 0] :rpy [0 0 0] :def obj
   :3d-res res3 :3d-points (render-boundary-points obj res3)
   :2d-costmap            (render-2d-costmap obj res2 inflate-hard inflate-soft)
   :2d-res res2 :2d-hard-rad inflate-hard :2d-soft-rad inflate-soft})

(defmulti object-def :class)
(defmethod object-def :box       [obj] obj)
(defmethod object-def :cylinder  [obj] obj)
(defmethod object-def :composite [obj] obj)
(defmethod object-def :rendered  [obj] (object-def (:def obj)))

(defn my-mod 
  "Given doubles d, r, return int & double so that (int * r + double) = d,
   and double has as small absolute value as possible."
  [d r]
  (let [li (int (Math/rint (double (/ d r))))]
    [li (- d (* li r))]))

(defn translate-points [pts [dx dy dz]]
  (let [dx (double dx) dy (double dy) dz (double dz)]
    (for [[x y z] pts]
      [(+ (double x) dx) (+ (double y) dy) (+ (double z) dz)])))

(defn translate-costmap [costmap [dx dy dz]]
  (let [dx (double dx) dy (double dy) dz (double dz)
	old-minx    (:minx costmap)
	old-miny    (:miny costmap)
	old-dx      (:dx costmap)
	old-dy      (:dy costmap)
	res         (:res costmap)
	[tx new-dx] (my-mod (+ old-dx dx) res)
	[ty new-dy] (my-mod (+ old-dy dy) res)]
;    (println dx dy dz old-dx old-dy tx new-dx ty new-dy)
    (assoc costmap 
      :minx (+ old-minx tx)
      :miny (+ old-miny ty)
      :dx new-dx :dy new-dy)))

(defn do-transform [t]
  (let [{:keys [xyz rpy def]} t]
    (assert (= rpy [0 0 0]))
    (assert (= (:class def) :rendered))
    (assoc def
      :xyz        (map + (:xyz def) xyz)
      :3d-points  (translate-points (:3d-points def) xyz)
      :2d-costmap (translate-costmap (:2d-costmap def) xyz))))
		      
      


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Composite ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod render-boundary-points :composite [obj res]
  (apply concat
    (for [part (vals (:parts obj))]
      (let [{:keys [xyz rpy def]} part]
	(assert (= rpy [0 0 0]))
	(translate-points (render-boundary-points def res) xyz)))))

(defmethod render-2d-costmap :composite [obj res hard-rad soft-rad]
  (let [costmaps      (for [part (vals (:parts obj))]
			(let [{:keys [xyz rpy def]} part]
			  (assert (= rpy [0 0 0]))
			  (translate-costmap (render-2d-costmap def res hard-rad soft-rad) xyz)))
	fminx     (int (apply min (map :minx costmaps)))
	fminy     (int (apply min (map :miny costmaps)))
	fmaxx     (int (apply max (map #(+ (:minx %) (:width %)) costmaps)))
	fmaxy     (int (apply max (map #(+ (:miny %) (:height %)) costmaps)))
	fwidth    (int (- fmaxx fminx))
	fheight   (int (- fmaxy fminy))
	#^bytes fdata (make-array Byte/TYPE (* fwidth fheight))]
    (doseq [costmap costmaps]
      (let [{:keys [minx miny width height data]} costmap
	    minx (int minx) miny (int miny) width (int width) height (int height)
	    #^bytes data data]
	(loop [y (int 0) fy (int (- miny fminy))]
	  (when (< y height)
	    (loop [x (int 0) fx (int (- minx fminx))]
	      (when (< x width)
		(let [v  (byte (aget data  (int (+ x  (* y  width)))))
		      fv (byte (aget fdata (+ fx (* fy fwidth))))]
		  (when (> (bit-and 255 (int v)) (bit-and 255 (int fv)))
		    (aset fdata (+ fx (* fy fwidth)) v)))
		(recur (inc x) (inc fx))))
	    (recur (inc y) (inc fy))))))
    (struct costmap fminx fminy res fwidth fheight fdata 0.0 0.0)))
		      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Box     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmethod render-boundary-points :box       [obj res]
  (let [size   (:size obj)
	pts    (map #(inc (int (/ % res))) size)
	org    (map #(- (/ (* (dec %) res) 2)) pts)
	opp    (map #(+ (/ (* (dec %) res) 2)) pts)
	[px py pz] pts
	[ox oy oz] org
	[fx fy fz] opp
	result (java.util.ArrayList.)]
    (doseq [x (range px) y (range py)]
      (let [x (+ ox (* x res)) y (+ oy (* y res))]
	(.add result [x y oz])
	(when (> pz 1) (.add result [x y fz]))))
    (doseq [x (range px) z (range 1 (dec pz))]
      (let [x (+ ox (* x res)) z (+ oz (* z res))]
	(.add result [x oy z])
	(when (> py 1) (.add result [x fy z]))))
    (doseq [y (range 1 (dec px)) z (range 1 (dec pz))]
      (let [y (+ oy (* y res)) z (+ oz (* z res))]
	(.add result [ox y z])
	(when (> px 1) (.add result [fx y z]))))
    (seq result)))


(defn drop-box [#^bytes arr width minx miny maxx maxy]
  (let [maxx (int maxx) maxy (int maxy) width (int width)]
    (loop [y (int miny)]
      (when (< y maxy)	
	(loop [x (int minx)]
	  (when (< x maxx)
	    (aset arr (+ x (* y width)) (byte 254))
	    (recur (inc x))))
	(recur (inc y))))))

(defn drop-circle [#^bytes arr width minx miny maxx maxy ox oy rad]
  (let [maxx (int maxx) maxy (int maxy) width (int width)
	ox   (int ox)   oy   (int oy)   rad2  (int (* rad rad))]
    (loop [y (int miny)]
      (when (< y maxy)	
	(loop [x (int minx)]
	  (when (< x maxx)
	    (let [dy (- oy y)
		  dx (- ox x)]
	      (when (<= (+ (* dy dy) (* dx dx)) rad2)
		(aset arr (+ x (* y width)) (byte 254))))
	    (recur (inc x))))
	(recur (inc y))))))

(defmethod render-2d-costmap :box       [obj res hard-rad soft-rad]
  (assert (>= soft-rad hard-rad 0))
  (assert (= soft-rad hard-rad))
  (let [size   (:size obj)
	pts    (map #(inc (int (/ % res))) size)
	[iw ih] pts
	pad    (map #(+ % (* 2 hard-rad)) pts)
	[w h]  pad
	#^bytes data (make-array Byte/TYPE (* w h))]
    (drop-box    data w hard-rad hard-rad (+ hard-rad iw) (+ hard-rad ih))
    (doseq [ix [0 (+ iw hard-rad)]]
      (drop-box data w ix hard-rad (+ ix hard-rad) (+ ih hard-rad)))
    (doseq [iy [0 (+ ih hard-rad)]]
      (drop-box data w hard-rad iy (+ iw hard-rad) (+ iy hard-rad)))
    (doseq [[sy fy oy] 
	      [[0 hard-rad hard-rad] 
	       [(+ ih hard-rad) (+ ih (* 2 hard-rad)) (dec (+ ih hard-rad))]]]
      (doseq [[sx fx ox] 
	        [[0 hard-rad hard-rad] 
		 [(+ iw hard-rad) (+ iw (* 2 hard-rad)) (dec (+ iw hard-rad))]]]
	(drop-circle data w sx sy fx fy ox oy hard-rad)))
    (struct costmap (int (/ w -2)) (int (/ h -2)) res w h data 0.0 0.0)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cylinder  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn circle-points [rad res]
  (let [pr (int (/ rad res))
	rad2 (* pr pr)]
    (for [py (range (- pr) (inc pr))
	  px (range (- pr) (inc pr))
	  :when (<= (+ (* px px) (* py py)) rad2)]
      [(* res px) (* res py)])))

(defn circle-boundary-points [rad res]
  (let [cp (circle-points (int (/ rad res)) 1)
	cps (set cp)]
    (for [p cp
	  :when (some #(not (cps (map + % p))) [[0 1] [0 -1] [1 0] [-1 0]])]
      (map #(* res %) p))))
  
(defmethod render-boundary-points :cylinder [obj res]
  (let [rad          (:radius obj)
	height       (:height obj)
	disk         (circle-points rad res)
	circle       (circle-boundary-points rad res)
	h            (inc (int (/ height res)))
	oz           (- (/ (* (dec h) res) 2))
	fz           (+ (/ (* (dec h) res) 2))
	result       (java.util.ArrayList.)]
    (doseq [z (cons oz (when (> h 1) [fz]))
	    xy disk]
      (.add result (conj xy z)))
    (doseq [z (range 1 (dec h))
	    :let [z (+ oz (* z res))]
	    xy circle]
      (.add result (conj xy z)))
    (seq result)))

(defmethod render-2d-costmap :cylinder [obj res hard-rad soft-rad]
  (assert (>= soft-rad hard-rad 0))
  (assert (= soft-rad hard-rad))
  (let [rad          (:radius obj)
	int-rad      (int (/ rad res))
	inf-rad      (+ int-rad hard-rad)
	dim          (inc (* 2 inf-rad))
	#^bytes data (make-array Byte/TYPE (* dim dim))]
    (drop-circle data dim 0 0 dim dim inf-rad inf-rad inf-rad)
    (struct costmap (- inf-rad) (- inf-rad) res dim dim data 0.0 0.0)))










;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Objects, etc. ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(defmulti fill-costmap (fn [obj #^bytes arr width height origin res inflation

(defn pre-render-world [w d3-res d2-res d2-pad]
  (into {} (map (fn [[k v]] [k (update-in v [:def] render-object d3-res d2-res d2-pad d2-pad)]) w)))


(def *voxel-res* 0.01)

(defn get-cup []
  {:class :cylinder :name "cup"
   :radius 0.025 
   :height 0.075})

(defn get-desk [] 
  {:class :composite :name "table"
   :parts
     {"table-top"
      {:xyz  [0 0 0.6] :rpy  [0 0 0]
       :def {:class :box :name "table-top" :size [0.75 1.5 0.10]}}
      "table-leg" 
      {:xyz  [0 0 0.3] :rpy  [0 0 0]
       :def {:class :box :name "table-leg" :size [0.05 0.05 0.60]}}
      "table-base"
      {:xyz  [0 0 0.6] :rpy  [0 0 0]
       :def {:class :box :name "table-base" :size [0.5 0.8 0.05]}}}})

(defn get-weird []
  {:class :composite :name "weird"
   :parts 
     {"rect"
      {:xyz [0 0 0] :rpy [0 0 0]
       :def {:class :box :name "rect" :size [6 4 1]}}
      "circ"
      {:xyz [3 2 2] :rpy [0 0 0]
       :def {:class :cylinder :radius 2 :height 5}}}})
   

; Hack in goals: 
; surface should be usable surface ...

(defn preprocess-world [w d3-res d2-res d2-pad]
  "Render the world, check object properties, and normalize goals."
  (let [w (pre-render-world w d3-res d2-res d2-pad)]
    (into {}
      (for [[obj-name info] w]
	[obj-name 
	 (condp = (:type info) 
	   :surface 
	     (do (assert (region-contains? (:surface info) (butlast (:xyz info))))
		 (assert (:height info))
		 (assert (not (:goal info)))
		 info)
	   :movable
	     (do (assert (:height info))
	         (assert (:on info))
		 (assert (= :surface (:type (w (:on info)))))		 
		 (assert (region-contains? (:surface (w (:on info))) (butlast (:xyz info))))
		 (assert (> (last (:xyz info)) (:height (w (:on info)))))
		 (if-let [[t & args] (:goal info)]
		   (assoc info :goal
		     [t
		       (let [goal-surface (:surface (w t))
			     padded-surface (shrink-xy-region goal-surface 0.1)]
			 (condp = (count args)
			   0 padded-surface
			   1 (do (assert (region-subsumes? padded-surface (first args)))
				 (first args))
			   2 (do (assert (region-contains? padded-surface args))
				 (make-xy-region [(first args) (first args)] [(second args) (second args)]))))])
		   info)))]))))
						      
    

(def *gazebo-offset* 25.65)
(defn get-simple-world [d3-res d2-res d2-pad]
  (preprocess-world 
   {"cup"   {:xyz [(+ *gazebo-offset* 2.35) (+ *gazebo-offset* 0) 0.6875] :rpy [0 0 0] :def (get-cup)
	     :type :movable :on "table" :goal ["table" ] :height 0.075
	     }
    "table" {:xyz [(+ *gazebo-offset* 2.28) (+ *gazebo-offset* -0.21) 0]  :rpy [0 0 0] :def (get-desk)
	     :type :surface :surface (make-xy-region [26 29] [25 26]) :height 0.605
	     }}
   d3-res d2-res d2-pad))
  
(defn get-odwalla [] {:class :cylinder :radius 0.04 :height 0.2})

(defn get-demo-world [d3-res d2-res d2-pad]
  (preprocess-world 
   {"table" {:xyz [17.48 26.55 0.378]  :rpy [0 0 0] 
	     :def {:class :box :name "table-top" :size [2.76 1.36 0.756]}
	     :type :surface :surface (make-xy-region [16.10 18.86] [25.87 27.23]) 
	     :height 0.756}
    "bottle" {:xyz [16.2 26.0 0.85] :rpy [0 0 0] :def (get-odwalla)
	     :type :movable :on "table" :goal ["table" (make-xy-region [17.2 17.4] [26.0 26.1])] :height 0.2}
    "bottle2" {:xyz [16.2 27.1 0.85] :rpy [0 0 0] :def (get-odwalla)
	     :type :movable :on "table" :goal ["table" (make-xy-region [17.2 17.4] [26.0 26.1])] :height 0.2}
    }
      d3-res d2-res d2-pad))

;; Coordinates for big table, 

 ; kitchen

;[16.169146525325775 27.25444436618952 0.7661073682977223] ; window tv
;[18.870676770772384 27.197025498543947 0.7563681210328691] ; window odwalla
;[18.846492327482324 25.82203319478116 0.7479274700544063] ; tv whiteboard
;[16.033881385488314 25.926735309868786 0.7708749146139766] ; kitchen
; table is 0.7036 in base_link, 0.7546 in /map


(defn world-points [w] 
  (mapcat 
   (fn [{:keys [xyz rpy def]}]
     (assert (= rpy [0 0 0]))
     (:3d-points (translate-points def xyz)))
   (vals w)))


; TODO: is this the correct def for extent?
(defn world-boxes [w]
  (mapcat 
   (fn [{:keys [xyz rpy def]}]
     (assert (= rpy [0 0 0]))
     (assert (= (:class def) :rendered))
     (let [res    (safe-get* def :3d-res)
	   extent {:class Point32 :x res :y res :z res}
	   axis   {:class Point32 :x 0 :y 0 :z 1}]
       (for [[x y z] (translate-points (safe-get* def :3d-points) xyz)]
	 {:class OrientedBoundingBox
	  :center {:class Point32 :x x :y y :z z}
	  :extents extent
	  :axis   axis
	  :angle  0})))
   (vals w)))

(defn world->collision-map [w]
  {:class  CollisionMap
   :header {:class Header :frame_id "/map" :stamp (.subtract (.now *ros*) (Duration. 0.1))}
   :boxes  (world-boxes w)})



(defn make-empty-collision-map []
  {:class CollisionMap 
   :header {:class Header :frame_id "/map" :stamp (.subtract (.now *ros*) (Duration. 0.1))}
   :boxes []})

;(def *kitchen-boxes*


(defn world-2d-res [w]
  (let [res (map #(:2d-res (:def %)) (vals w))]
    (assert (apply = res))
    (first res)))

(defn world->costmap [w [minx miny] [maxx maxy]]
  (let [res     (world-2d-res w)
	fminx (int (/ minx res)) fminy (int (/ miny res))
	fmaxx (int (/ maxx res)) fmaxy (int (/ maxy res))
	fwidth (int (- fmaxx fminx))
	fheight (int (- fmaxy fminy))
	#^bytes fdata (make-array Byte/TYPE (* fwidth fheight))]
    (doseq [{:keys [xyz rpy def]} (vals w)]
      (assert (= (:class def) :rendered))
      (assert (= rpy [0 0 0]))
      (let [costmap (translate-costmap (:2d-costmap def) xyz)
	    {:keys [minx miny width height data]} costmap
	    minx (int minx) miny (int miny) width (int width) height (int height)
	    #^bytes data data]
	(assert (= (:res costmap) res))
	(loop [y (int (max 0 (- fminy miny))) fy (int (+ y (- miny fminy)))]
	  (when (and (< y height) (< fy fheight))
	    (loop [x (int (max 0 (- fminx minx))) fx (int (+ x (- minx fminx)))]
	      (when (and (< x width) (< fx fwidth))
		(let [v  (byte (aget data  (int (+ x  (* y  width)))))
		      fv (byte (aget fdata (+ fx (* fy fwidth))))]
		  (when (> (bit-and 255 (int v)) (bit-and 255 (int fv)))
		    (aset fdata (+ fx (* fy fwidth)) v)))
		(recur (inc x) (inc fx))))
	    (recur (inc y) (inc fy))))))
    {:class SetCostmap$Request
     :costs fdata
     :height fheight
     :width fwidth}))

(defn print-costmap-message [msg]
  (print-2d-costmap {:data (:costs msg) :width (:width msg)}))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Future base planning. ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Test for tf-node frame stuff



; (put-single-message "start_static_transform" (map-msg {:class StartStaticTransform :frame_id "/future_base_link" :parent_id "/base_link" :frequency (Duration. 1.0)  :transform {:class Transform :translation {:class Vector3 :x 1 :y 2 :z 3} :rotation {:class Quaternion :x 0 :y 0 :z 0 :w 1}}}))

; (put-single-message "collision_map_future" (map-msg (world->collision-map (get-initial-world 0.1))))




; (put-single-message "publish_transform" (map-msg {:class TransformStamped :header {:class Header :frame_id "tmp"} :parent_id "tmp2" :transform {:class Transform :translation {:class Vector3 :x 1 :y 2 :z 3} :rotation {:class Quaternion :x 1 :y 0 :z 0 :w 0}}}))

; (put-single-message "start_static_transform" (map-msg {:class StartStaticTransform :frame_id "test" :parent_id "foo" :frequency (Duration. 1.0)  :transform {:class Transform :translation {:class Vector3 :x 1 :y 2 :z 3} :rotation {:class Quaternion :x 1 :y 0 :z 0 :w 0}}}))



; Note right now, static transforms are dated 2x ahead of frequency to assure coverage.


;(defsrvs [ros.pkg.navfn.srv SetCostmap MakeNavPlan])

; (call-srv "/navfn_node/set_costmap" (map-msg {:class SetCostmap$Request :costs (repeat 100 (byte 0)) :height 10 :width 10}))

; (defn xy->pose-stamped [[x y]] {:class PoseStamped :header {:class Header :frame_id "/map"} :pose {:class Pose :position {:class Point :x x :y y :z 0} :orientation {:class Quaternion :x 0 :y 0 :z 0 :w 0}}})

; (call-srv "/navfn_node/make_plan" (map-msg {:class MakeNavPlan$Request :start (xy->pose-stamped [4 4]) :goal (xy->pose-stamped [7 7])}))

; (defn pose-stamped->xy [ps] (let [point (:position (:pose ps))] [(:x point) (:y point)]))

; (map pose-stamped->xy (:path (call-srv "/navfn_node/make_plan" (map-msg {:class MakeNavPlan$Request :start (xy->pose-stamped [4 4]) :goal (xy->pose-stamped [7 7])}))))

; (call-srv "/navfn_node/set_costmap" (map-msg {:class SetCostmap$Request :costs (map byte (concat (repeat 10 0) (repeat 5 0) (repeat 10 0))) :height 5 :width 5}))

; 254 is lethal, 253 seems lethal-like (inscribed obstacle), below is nonlethal?


(set! *warn-on-reflection* false)