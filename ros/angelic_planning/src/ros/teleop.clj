;///////////////////////////////////////////////////////////////////////////////
;// Useful utilities for teleoperation
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



(ns ros.teleop
  (:use   clojure.xml ros.ros ros.actions ros.world ros.geometry ros.robot)
    (:require [edu.berkeley.ai.util :as util])
	  )
  
(set! *warn-on-reflection* true)

(import-ros)


;; Head 

(defn look-r  [nh] (look-at nh [0 -2 1.2]))
(defn look-dr [nh] (look-at nh [0 -2 0.6]))
(defn look-rf  [nh] (look-at nh [2 -2 1.2]))
(defn look-drf [nh] (look-at nh [2 -2 0.6]))
(defn look-f  [nh] (look-at nh [2 0 1.2]))
(defn look-df [nh] (look-at nh [2 0 0.6]))
(defn look-lf  [nh] (look-at nh [2 2 1.2]))
(defn look-dlf [nh] (look-at nh [2 2 0.6]))
(defn look-l  [nh] (look-at nh [0 2 1.2]))
(defn look-dl [nh] (look-at nh [0 2 0.6]))
  

;; Base

(defn forward [nh x] (move-base-rel nh :x x))
(defn back    [nh x] (move-base-rel nh :x (- x)))
(defn left    [nh x] (move-base-rel nh :y x))
(defn right   [nh x] (move-base-rel nh :y (- x)))

(defn move-base [nh [x y theta]]
  (move-base-to-state nh (make-robot-base-state x y theta)))

; Arm

(defn move-arm-xzy [nh right? xyz]
  (move-arm-to-pose nh right? (make-pose xyz [0 0 0 1])))



;; move arm into grasping position using rviz


(defn compute-grasp-point [[x y z]]
  "Compute a good point for the gripper to grasp (palm link) given object coords in base link."
  (when (and (> x 0.4) (< x 1.5) (> y -0.5) (< y 0.5))
    [(- x 0.26) y z]));(+ z 0.12)]))

(defn arm-to-grasp "obj in base-link" [nh right? obj]
  (if-let [grasp-point (compute-grasp-point obj)]
    (do (println "Grasping to" grasp-point)
	(= :success (first (move-arm-to-pose nh right? (make-pose grasp-point [0 0 0 1]) "/base_link" false 20.0))))
    (println "Failed to get grasp point for" obj)))

(defn approx-= [x y tol] (< (Math/abs (double (- x y))) tol))

(defn final-approach "obj in base-link" [nh right? [objx objy objz]]
  (let [[[gx gy gz] [ox oy oz ow]] (get-arm-pose nh right?)]
;    (println ox gx)
    (assert (approx-= gy objy 0.05))
    (assert (approx-= ow 1.0 0.10))
    (move-base-rel nh :x (- objx gx 0.15) 1.0 #_0.5)
    true
    ))

(defn pt [x] (println x) x)

(defn grasp-object "obj in base-link" [nh right? obj]
  (and 
  ; (do (look-at nh obj) true)
   (do (pt (open-gripper nh right?)) true)
   (do (pt (arm-to-grasp nh right? obj)) true)
   (do (final-approach nh right? obj) true)
   (do (pt (close-gripper nh)) true)
   (do (Thread/sleep 3000) (move-base-rel nh :x -0.3) true)
   (pt (move-arm-to-state nh (arm-joint-state true "home") true 60.0))
;   (do (look-forward nh) true)))
   ))

(defn grasp-rviz [nh right?]
  (let [[obj-map obj-bl] (get-rviz-points nh true)]
    (grasp-object nh right? obj-bl)))

(comment 

(defmacro lazy []
  `(do 
     
     (defn ~'go-arm-ru 
       ([~'j] (~'go-arm-ru ~'j 1.0))  
       ([~'j ~'speed-mul]
	  (move-arm-directly-to-state ~'nh (arm-joint-state true ~'j) 10 (* 0.1 ~'speed-mul))))
     (defn ~'go-arm-traj 
       ([~'j] (~'go-arm-traj ~'j 1.0))
       ([~'j speed-mul#]
	  (execute-arm-trajectory ~'nh 
	    (if (map? ~'j) ~'j
	      (encode-normalized-arm-trajectory true ~'j (* speed-mul# 1)))
	    10)))
     (defn ~'go-arm-plan 
       ([~'j] (~'go-arm-plan ~'j false))
       ([~'j ~'upright?]
	  (move-arm-to-state ~'nh (arm-joint-state true ~'j) ~'upright? 30.0)))
     (defn ~'go-arm-pos
       ([~'j] (~'go-arm-pos ~'j false))
       ([~'j ~'upright?]
	  (move-arm-to-pos ~'nh ~'j ~'upright? 30.0)))
             
     (defn ~'open [] (open-gripper ~'nh))
     (defn ~'close ([] (~'close 60)) ([~'f] (close-gripper ~'nh ~'f false)))
     (defn ~'throw [] (do-throw ~'nh "_new"))

     (defn ~'homeu [] (~'go-arm-plan "home"))
     (defn ~'home [] (~'go-arm-plan "home" true))
     (defn ~'homeru [] (~'go-arm-ru "home"))
     
     (defn ~'face-bar [] (spin-base-to-bar ~'nh))
     (defn ~'face-window [] (spin-base-from-bar ~'nh))
     (defn ~'face-patio [] (spin-base-to ~'nh Math/PI))
     (defn ~'face-me [] (spin-base-to ~'nh 0))
     (defn ~'spin-tip [] (spin-base-rel ~'nh (/ Math/PI 5)))

     (defn ~'trash []  
       (~'go-base "trash") 
       (~'go-arm-traj *drop-traj2*)
       (~'open)
       (Thread/sleep 1000)
       (~'go-arm-plan "home"))
     
     (defn ~'stop [] (preempt-arm ~'nh) (preempt-base ~'nh))

     (defn ~'reset []  (.shutdown ~'nh) (def ~'nh (make-node-handle)))
     )))


(set! *warn-on-reflection* false)


(comment 

(defn wait-for-bottle [nh z]
  (laser-slow)
;  (Thread/sleep 2000)
  (loop [bottles (find-bottles nh z)]
    (if (empty? bottles)
        (do (print ".")
	    (Thread/sleep 100)
	    (recur (find-bottles nh z)))
      (do (future-call laser-fast)
	  (let [bottles (map #(decode-point (:point %)) bottles)]
	    (println "Got bottles" bottles)
	    (update-in 
	     (util/first-maximal-element 
	      #(- 100 (Math/abs (double (second %))))
	      bottles)
	     [2] - 0.02)
	    )))))

(defn compute-base-grasp-rect 
  "Given a rectangular table and point in map frame, compute a good base state along x edge.
   Return nil if no pose is thought feasible"
  [[[minx maxx] [miny maxy] tz] [x y z]]
  (assert (and (<= minx x maxx) (<= miny y maxy)))
  (let [min? (< (Math/abs (double (- miny y))) (Math/abs (double (- maxy y))))
	[dir edge] (if min? [-1 miny] [1 maxy])]
    (when (< (Math/abs (double (- edge y))) 0.5)
      (make-robot-base-state (- x (* dir 0.1)) (+ y (* dir 1.0)) (+ (/ Math/PI 2) (if min? 0 Math/PI))))))

(defn base-to-grasp-rect [nh table obj]
  (when-let [rect (compute-base-grasp-rect table obj)]
    (println "Trying to move to" rect)
    (= :success (move-base-to-state nh rect))
    ))

(defn base-rviz [nh table]
  (let [[obj-map obj-bl] (get-rviz-points nh true)]
    (base-to-grasp-rect nh table obj-map)))

(defn base-nearest [nh table ht]
  (base-to-grasp-rect nh table 
    (transform-point nh "/base_link" "/map" (wait-for-bottle nh ht))))


  

 )



(comment 
(defn get-trash-point [nh]
  (let [p (get-single-message-cached nh "/trash_can" (PointStamped.))]
    (transform-point nh (:frame_id (:header p)) "/base_link" (decode-point (:point p)))))

(defn servo-to-trash [nh]
  (spin-base-to-bar nh)
  (Thread/sleep 1000)
  (let [[x y] (get-trash-point nh)]
    (do (assert (< (Math/abs (double (- x 0.75))) 0.3))
	(move-base-rel nh :vx (- x 0.75)))))

(defn servo-to-sink [nh]
  (spin-base-to-bar nh)
  (Thread/sleep 1000)
  (let [[x y] (get-trash-point nh)]
    (do (assert (< (Math/abs (double (- x 0.65))) 0.3))
	(move-base-rel nh :vx (- x 0.65)))))

(defn servo-to-bar [nh]
  (spin-base-to-bar nh)
  (Thread/sleep 1000)
  (let [[x y] (get-trash-point nh)]
    (do (assert (< (Math/abs (double (- x 0.75))) 0.3))
	(move-base-rel nh :vx (- x 0.75)))))
  )


(comment 


(defn grasp-nearest [nh ht]
  (grasp-object nh (wait-for-bottle nh ht)))


(defn move-and-grasp-rviz [nh table]
  (let [[obj-map obj-bl] (get-rviz-points nh true)
	obj-odom (transform-point nh "/map" "/odom" obj-map)]
    (if (base-to-grasp-rect nh table obj-map)
        (let [obj-bl-new (do (Thread/sleep 1000) (transform-point nh "/odom" "/base_link" obj-odom))]
	  (grasp-object nh obj-bl-new))
      (println "Base movement failed; not attempting grasp."))))
 )



(comment 
(defn shake-drink [nh]
  (let [cs (get-current-arm-state nh true)
	a  (/ Math/PI 8) 
	t  0.3
	ns (update-in cs  [:joint-angle-map "r_wrist_roll_joint"] - a)
	ps (update-in cs  [:joint-angle-map "r_wrist_roll_joint"] + a)]
    (move-arm-directly-to-state nh ns t 100)
    (move-arm-directly-to-state nh ps t 100)
    (move-arm-directly-to-state nh ns t 100)
    (move-arm-directly-to-state nh ps t 100)
    (move-arm-directly-to-state nh cs t 100)))

  )