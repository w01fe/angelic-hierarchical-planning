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


(defmsgs  [robot_msgs PointStamped PoseStamped PoseWithRatesStamped])




(defn l2-distance [v1 v2]
   (Math/sqrt (reduce + (map #(let [x (- (double %1) (double %2))] (* x x)) v1 v2))))


(defn angle->quaternion [rads]
  {:class Quaternion
   :x 0 :y 0 :z (Math/sin (double (/ rads 2))) :w (Math/cos (double (/ rads 2)))})

(defn quaternion->angle [orientation]
  (assert (< (Math/abs (double (:x orientation))) 0.001))
  (assert (< (Math/abs (double (:y orientation))) 0.001))
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
     :position (add-points (apply-rotation q2 p1) p2)
     :orientation (multiply-quaternions q2 q1)}))

(defn untransform-pose [init-pose pose-transform]
  (let [p1 (:position init-pose) q1 (:orientation init-pose)
	p2 (:position pose-transform) q2 (:orientation pose-transform)
	q2i (invert-unit-quaternion q2)]
    {:class Pose
     :position (apply-rotation (subtract-points p1 p2) q2i)
     :orientation (multiply-quaternions q2i q1)}))

(def *null-transform-pose* 
     {:class Pose 
      :position    {:x 0 :y 0 :z 0}
      :orientation {:x 0 :y 0 :z 0 :w 1}})


(defn make-point [[x y z]]
  {:class Point :x x :y y :z z})

(defn make-quaternion [[x y z w]]
  {:class Quaternion :x x :y y :z z :w w})

(defn make-pose [[x y z] [qx qy qz qw]]
  {:class Pose 
   :position    (make-point [x y z])
   :orientation (make-quaternion [qx qy qz qw])})

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






(set! *warn-on-reflection* false)


