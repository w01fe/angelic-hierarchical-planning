;///////////////////////////////////////////////////////////////////////////////
;// Robot state for high-level planning.
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



(ns ros.geometry
  (:use   ros.ros)
	  )
  
(set! *warn-on-reflection* true)

(import-ros)

(defmsgs  [geometry_msgs PointStamped PoseStamped])
(defsrvs  [tf_node TransformPoint TransformPose])




(defn l2-distance [v1 v2]
   (Math/sqrt (reduce + (map #(let [x (- (double %1) (double %2))] (* x x)) v1 v2))))


(defn norm-angle [a]
  "Normalize the angle to be between -Pi and Pi"
  (cond (> a (+ Math/PI 0.0000001)) (recur (- a (* 2 Math/PI)))
	(< a (- -0.0000001 Math/PI)) (recur (+ a (* 2 Math/PI)))
	:else a))

(defn angle->quaternion [rads]
  {:class Quaternion
   :x 0 :y 0 :z (Math/sin (double (/ rads 2))) :w (Math/cos (double (/ rads 2)))})

(defn quaternion->angle [orientation]
  (assert (< (Math/abs (double (:x orientation))) 0.05))
  (assert (< (Math/abs (double (:y orientation))) 0.05))
  (let [r (* 2 (Math/atan2 (double (:z orientation)) (double (:w orientation))))]
    (if (< r 0) (+ r (* Math/PI 2)) r)))

(defn axis-angle->quaternion [[x y z] a]
  (let [n (l2-distance [x y z] [0 0 0])
	s (Math/sin (double (/ a 2.0)))
	d (/ s n)]
    [(* x d) (* y d) (* z d) (Math/cos (double (/ a 2.0)))]))

(defn axis-angle->quaternion-msg [[x y z] a]
  (let [n (l2-distance [x y z] [0 0 0])
	s (Math/sin (double (/ a 2.0)))
	d (/ s n)]
    {:class Quaternion
     :x (* x d)
     :y (* y d)
     :z (* z d)
     :w (Math/cos (double (/ a 2.0)))}))

(defn quaternion-msg->axis-angle [msg]
  (let [a (* 2 (Math/acos (double (:w msg))))
	s (Math/sqrt (- 1 (double (* (:w msg) (:w msg)))))]
    (if (< s 0.0001)
        [[0 0 1] a]
      [[(/ (:x msg) s) (/ (:y msg) s) (/ (:z msg) s)] a])))

(defn multiply-quaternions [q1 q2]
  (let [a1 (:w q1) b1 (:x q1) c1 (:y q1) d1 (:z q1)
	a2 (:w q2) b2 (:x q2) c2 (:y q2) d2 (:z q2)]
    {:class Quaternion
     :w (- (* a1 a2) (* b1 b2) (* c1 c2) (* d1 d2))
     :x (+ (* a1 b2) (* b1 a2) (* c1 d2) (- (* d1 c2)))
     :y (+ (* a1 c2) (* c1 a2) (* d1 b2) (- (* b1 d2)))
     :z (+ (* a1 d2) (* d1 a2) (* b1 c2) (- (* c1 b2)))}))

(defn apply-rotation [p q]
  (let [x (:x p) y (:y p) z (:z p)
	a (:w q) b (:x q) c (:y q) d (:z q)
	t2 (* a b)
	t3 (* a c)
	t4 (* a d)
	t5 (- (* b b))
	t6 (* b c)
	t7 (* b d)
	t8 (- (* c c))
	t9 (* c d)
	t10 (- (* d d))]
    {:class Point
     :x (+ x (* 2 (+ (* x (+ t8 t10)) (* y (- t6 t4)) (* z (+ t3 t7)))))
     :y (+ y (* 2 (+ (* x (+ t4 t6)) (* y (+ t5 t10)) (* z (- t9 t2)))))
     :z (+ z (* 2 (+ (* x (- t7 t3)) (* y (+ t2 t9)) (* z (+ t5 t8)))))}))

(defn add-points [p1 p2]
  {:class Point 
   :x (+ (:x p1) (:x p2))
   :y (+ (:y p1) (:y p2))
   :z (+ (:z p1) (:z p2))})

(defn subtract-points [p1 p2]
  {:class Point 
   :x (- (:x p1) (:x p2))
   :y (- (:y p1) (:y p2))
   :z (- (:z p1) (:z p2))})

(defn invert-unit-quaternion [q]
  (assoc q :w (- (:w q))))


(defn transform-pose [init-pose pose-transform]
  (let [p1 (:position init-pose) q1 (:orientation init-pose)
	p2 (:position pose-transform) q2 (:orientation pose-transform)]
    {:class Pose
     :position (add-points (apply-rotation p1 q2) p2)
     :orientation (multiply-quaternions q2 q1)}))

(defn untransform-pose [init-pose pose-transform]
  (let [p1 (:position init-pose) q1 (:orientation init-pose)
	p2 (:position pose-transform) q2 (:orientation pose-transform)
	q2i (invert-unit-quaternion q2)]
    {:class Pose
     :position (apply-rotation (subtract-points p1 p2) q2i)
     :orientation (multiply-quaternions q2i q1)}))`

(def *null-transform-pose* 
     {:class Pose 
      :position    {:x 0 :y 0 :z 0}
      :orientation {:x 0 :y 0 :z 0 :w 1}})


(defn make-point [[x y z]]
  {:class Point :x x :y y :z z})

(defn decode-point [p]
  [(:x p) (:y p) (:z p)])

(defn make-quaternion [[x y z w]]
  {:class Quaternion :x x :y y :z z :w w})

(defn decode-quaternion [p]
  [(:x p) (:y p) (:z p) (:w p)])

(defn make-pose [[x y z] [qx qy qz qw]]
  {:class Pose 
   :position    (make-point [x y z])
   :orientation (make-quaternion [qx qy qz qw])})

(defn decode-pose [p]
  [(decode-point (:position p))
   (decode-quaternion (:orientation p))])

(defn pose-position [pose]
  (let [{{:keys [x y z]} :position} pose]
    [x y z]))

(defn pose-aa [pose]
  (quaternion-msg->axis-angle (:orientation pose)))


(defn point-distance [p1 p2]
  (let [vecs (map #(map % [:x :y :z]) [p1 p2])]
    (Math/sqrt (double (apply + (apply map #(* (- %1 %2) (- %1 %2)) vecs))))))

(defn orientation-distance [o1 o2]
  (let [a  (* 2 (Math/acos (apply + (apply map * (map #(map % [:x :y :z :w]) [o1 o2])))))]
    (if (< a (Math/PI)) a (- (* 2 Math/PI) a))))

(defn pose-distance [p1 p2 angle-wt]
  (let [pd (point-distance (:position p1) (:position p2))
	od (orientation-distance (:orientation p1) (:orientation p2))]
  ;  (println pd od)
    (+ pd (* angle-wt od)))) 


(defn transform-point-tf [nh src-frame trg-frame nice-point]
  (decode-point 
   (:point (:pout 
     (call-srv nh "/tf_node/transform_point"
	       (map-msg TransformPoint$Request
			{:target_frame trg-frame
			 :target_time (Time.);(.subtract (.now *ros*) (Duration. 0.3))
			 :pin {:header {:frame_id src-frame :stamp (.subtract (.now *ros*) (Duration. 0.3))}
			       :point (make-point nice-point)}
			 :fixed_frame ""})
	       )))))

(defn transform-raw-pose-tf [nh src-frame trg-frame pose]
   (:pose (:pout 
     (call-srv nh "/tf_node/transform_pose"
	       (map-msg TransformPose$Request
			{:target_frame trg-frame
			 :target_time (Time.);(.subtract (.now *ros*) (Duration. 0.3))
			 :pin {:header {:frame_id src-frame :stamp (.subtract (.now *ros*) (Duration. 0.3))}
			       :pose pose}
			 :fixed_frame ""})
	       ))))

(defn transform-pose-tf [nh src-frame trg-frame nice-pose]
  (decode-pose (transform-raw-pose-tf nh src-frame trg-frame (apply make-pose nice-pose))))


;; Regions

(defmulti region-name :class)

(defmulti sample-region :class)

(defmulti region-contains? (fn [i p] (:class i)))

(defmulti region-subsumes? (fn [x y] [(:class x) (:class y)]))


(defn rand-double [[mn mx]]
  (+ mn (rand (- mx mn))))



(defn make-interval-region [[a b]]
  (assert (>= b a))
  {:class ::IntervalRegion :interval [a b]})

(defmethod sample-region ::IntervalRegion [r]
  (rand-double (:interval r)))

(defmethod region-name ::IntervalRegion [r]
  (:interval r))

(defmethod region-contains? ::IntervalRegion [r p]
  (let [[a b] (:interval r)] 
    (<= a p b)))

(defmethod region-subsumes? [::IntervalRegion ::IntervalRegion] [x y]
  (let [[ax bx] (:interval x) 
        [ay by] (:interval y)] 
    (<= ax ay by bx)))

(defn shrink-interval-region [r e]
  (let [[a b] (:interval r)]
    (make-interval-region [(+ a e) (- b e)])))


(defn make-xy-region [[minx maxx] [miny maxy]]
  {:class ::XYRegion
   :intervals [(make-interval-region [minx maxx])
	       (make-interval-region [miny maxy])]})

(defmethod sample-region ::XYRegion [r]
  (vec (map sample-region (:intervals r))))

(defmethod region-name ::XYRegion [r]
  (vec (map region-name (:intervals r))))

(defmethod region-contains? ::XYRegion [r p]
  (every? identity (map region-contains? (:intervals r) p)))

(defmethod region-subsumes? [::XYRegion ::XYRegion] [x y]
  (every? identity (map region-subsumes? (:intervals x) (:intervals y))))

(defn get-xy-region-extent [r]
  (map :interval (:intervals r)))

(defn get-xy-region-point-stamped [r height]
  (let [[[ax bx] [ay by]] (get-xy-region-extent r)]
    {:class PointStamped
     :header {:frame_id "/map"}
     :point  (make-point (/ (+ ax bx) 2) (/ (+ ay by) 2) height)}))


(defn shrink-xy-region [r e]
  (update-in r [:intervals] (fn [is] (map #(shrink-interval-region % e) is))))


(defn make-xytheta-region [[minx maxx] [miny maxy] [mina maxa]]
  {:class ::XYThetaRegion
   :intervals [(make-interval-region [minx maxx])
	       (make-interval-region [miny maxy])
	       (make-interval-region [mina maxa])]})

(defmethod sample-region ::XYThetaRegion [r]
  (vec (map sample-region (:intervals r))))

(defmethod region-name ::XYThetaRegion [r]
  (vec (map region-name (:intervals r))))

(defmethod region-contains? ::XYThetaRegion [r p]
  (every? identity (map region-contains? (:intervals r) p)))

(defmethod region-subsumes? [::XYThetaRegion ::XYThetaRegion] [x y]
  (every? identity (map region-subsumes? (:intervals x) (:intervals y))))

(defn get-xy-theta-region-point-stamped [r]
  (let [[[ax bx] [ay by]] (get-xy-region-extent r)]
    {:class PointStamped
     :header {:frame_id "/map"}
     :point  (make-point (/ (+ ax bx) 2) (/ (+ ay by) 2) 0)}))





(comment 
(defn make-surface-region [[minx maxx] [miny maxy] z]
  {:class ::SurfaceRegion
   :intervals [(make-interval-region [minx maxx])
	       (make-interval-region [miny maxy])]
   :z z})

(defmethod sample-region ::SurfaceRegion [r]
  (vec (concat (map sample-region (:intervals r)) [(:z r)])))

(defmethod region-name ::SurfaceRegion [r]
  (vec (concat (map region-name (:intervals r)) [(:z r)])))

(defmethod region-contains? ::SurfaceRegion [r p]
  (let [[p1 p2 p3] p
	{[i1 i2] :intervals z :z} r]
    (and (region-contains? i1 p1) (region-contains? i2 p2) (= p3 z))))

(defmethod region-subsumes? [::SurfaceRegion ::SurfaceRegion] [x y]
  (let [{[x1 x2] :intervals z1 :z} x
	{[y1 y2] :intervals z2 :z} y]
    (and (region-subsumes? x1 y1) (region-subsumes? x2 y2) (= z1 z2))))

 )


(comment 
(defn make-linear-spline-trajectory 
  ([init-joints final-joints]
     (make-linear-spline-trajectory init-joints final-joints 0.2))
  ([init-joints final-joints time]
;     (println init-joints final-joints)
     (assert (= (set (keys init-joints)) (set (keys final-joints))))
     (let [kys (keys init-joints)]
       {:class SplineTraj :header *tll-header* :names kys
	:segments [{:duration (Time. (double time))
		    :a (map final-joints kys)
		    ;:b (map #(/ (- (final-joints %) (init-joints %)) (double time)) kys)
		    :b (repeat 6 0.0) :c (repeat 6 0.0) :d (repeat 6 0.0) :e (repeat 6 0.0) :f (repeat 6 0.0)}]})))
 )


(set! *warn-on-reflection* false)





  