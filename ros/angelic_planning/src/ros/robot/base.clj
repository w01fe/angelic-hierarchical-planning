;///////////////////////////////////////////////////////////////////////////////
;// Robot state (base).
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



(in-ns 'ros.robot)
  
(defmsgs [std_msgs Empty]
         [geometry_msgs PoseWithCovarianceStamped PointStamped Twist]
         [nav_robot_actions MoveBaseState])

(defsrvs  [navfn SetCostmap MakeNavPlan])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base States, getters ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def *current-base-pose* (atom nil))
(def *base-pose-sub* (atom nil))

(defstruct robot-base-state    :class :x :y :theta)

(defn make-robot-base-state [x y theta]
  (struct robot-base-state ::BaseState x y theta))

(defmethod get-joint-map ::BaseState [obj]
  {"base_joint" [(:x obj) (:y obj) (:theta obj)]})


(defn pose->base-state [pose-stamped]
  (when-not (or (= (:class pose-stamped) Pose) (not (map? pose-stamped)))
    (assert (#{"map" "/map"} (:frame_id (:header pose-stamped)))))
  (let [pose (condp = (:class pose-stamped)
	       Pose                 pose-stamped
	       PoseWithCovariance   (:pose pose-stamped)
	       PoseStamped          (:pose pose-stamped)
	       nil                  (do (assert (not (map? pose-stamped))) (apply make-pose pose-stamped))
	       ;PoseWithRatesStamped (:pose (:pose_with_rates pose-stamped))
	       )]
    (make-robot-base-state
     (:x (:position pose))
     (:y (:position pose))
     (quaternion->angle (:orientation pose)))))

(defn base-state->pose-stamped [base-state]
  {:class PoseStamped
   :header {:frame_id "/map"}
   :pose   {:position {:x (:x base-state) :y (:y base-state) :z 0}
	    :orientation (angle->quaternion (:theta base-state))}})


(defn base-state->point-stamped [base-state]
  {:class PointStamped
   :header {:frame_id "/map"}
   :point {:x (:x base-state) :y (:y base-state) :z 0}})




(let [mem (atom {})]
  (def get-current-base-pose 
     (fn [#^NodeHandle nh]
       (let [a 
	     (or (@mem nh)
		 (let [a (atom nil)]
		   (.subscribe nh "/amcl_pose" (PoseWithCovarianceStamped.)
				      (sub-cb [m] (reset! a (:pose (:pose m)))) 1)
;		   (.subscribe nh "/base_pose_ground_truth" (PoseWithRatesStamped.)
;				      (sub-cb [m] (reset! a (:pose (:pose_with_rates m)))) 1)
		   (swap! mem assoc nh a)
		   a))]
	 (.spinOnce nh)
	 (while (not @a) (.spinOnce nh))
	 @a))))

(let [mem (atom {})]
  (def get-current-base-odom
     (fn [#^NodeHandle nh]
       (let [a 
	     (or (@mem nh)
		 (let [a (atom nil)]
		   (.subscribe nh "/robot_pose_ekf/odom_combined" (PoseWithCovarianceStamped.)
			       (sub-cb [m] (reset! a (:pose (:pose m)))) 1)
;		   (.subscribe nh "/base_pose_ground_truth" (PoseWithRatesStamped.)
;				      (sub-cb [m] (reset! a (:pose (:pose_with_rates m)))) 1)		   
		   (swap! mem assoc nh a)
		   a))]
	 (.spinOnce nh)
	 (while (not @a) (.spinOnce nh))
	 @a))))



(defn get-current-base-state-tf [nh] 
  (pose->base-state (transform-pose-tf nh "/base_link" "/map" [[0 0 0] [0 0 0 1]])))

(defn get-current-base-state [#^NodeHandle nh]
  (get-current-base-state-tf nh))
;  (pose->base-state (get-current-base-pose nh)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Moving using move_base ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
 
(defn move-base-to-pose-stamped 
  "Moves the base to the given pose-stamped, by invoking move_base."
  ([#^NodeHandle nh pose]
     (laser-fast)
     (run-old-action nh "/move_base" (map-msg pose) (MoveBaseState.) (Duration. 60.0))))

(defn move-base-to-state
  "Like move-base-to-pose-stamped, but takes a robot-base-state"
  ([nh state]
     (move-base-to-pose-stamped nh (base-state->pose-stamped state))))

(defn move-base-forward
  "Moves base forward using move_base."
  [#^NodeHandle nh distance]
  (let [{:keys [x y theta]} (get-current-base-state nh)
	theta (double theta)]
    (move-base-to-state nh (make-robot-base-state (+ x (* distance (Math/cos theta)))
						  (+ y (* distance (Math/sin theta)))
						  theta))))

(defn preempt-base [nh]
  (put-single-message nh "/move_base/preempt" (Empty.) 1))		       

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; Moving unsafely using controller ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- move-base-unsafe 
  "Custom interface for moving base directly, without move_base."
  ([#^NodeHandle nh command-fn goal-fn]
     (move-base-unsafe nh command-fn goal-fn 5.0))
  ([#^NodeHandle nh command-fn goal-fn timeout]
  (let [pub (.advertise nh "/cmd_vel" (Twist.) 1)
	sw  (util/start-stopwatch)]
    (let [init-pose (get-current-base-odom nh)
	  init-pos (:position init-pose)
	  zero     {:x 0 :y 0 :z 0}]
      (loop []
	(let [current-pose (get-current-base-odom nh)]
  	 (when (and (util/within-time-limit? sw timeout)
		    (not (goal-fn init-pose current-pose)))
	  (.publish pub (map-msg Twist (update-in 
					  (update-in 
					   (command-fn init-pose current-pose)
					   [:linear] #(merge zero %))
					   [:angular] #(merge zero %))))
	  (Thread/sleep 100)
	  (recur))))
      (.publish pub (map-msg Twist {:linear zero :angular zero}))
      (println "Stopping: traveled" (point-distance init-pos (:position (get-current-base-odom nh))))
      )
    (.shutdown pub))))


(defn move-base-rel
  "Directly moves using base controllers (unsafe), without invoking planning."
  ([#^NodeHandle nh coord distance] (move-base-rel nh coord distance 1.0))
  ([#^NodeHandle nh coord distance speed] (move-base-rel nh coord distance speed 5.0))
  ([#^NodeHandle nh coord distance speed timeout]
  (assert (#{:x :y} coord))
  (let [distance (double distance)
	dir (Math/signum distance)
	distance (Math/abs distance)]
   (move-base-unsafe nh
    (fn [init-pose current-pose]
      (let [dist (- distance (point-distance (:position init-pose) (:position current-pose)))]
	{:linear {coord (* dir (cond (> dist 0.2) (* speed 0.2) 
				  (< dist -0.2) 0
				  :else (* (max dist 0) speed 1.5)))}}))
    (fn [init-pose current-pose]
      (let [dist (- distance (point-distance (:position init-pose) (:position current-pose)))]
	(or (< (Math/abs (double dist)) 0.005)
	    (< dist -0.09))))
    timeout))))


(defn spin-base-to
  "Spins base to a desired angle, with no collision checking."
  [#^NodeHandle nh angle]
  (let [init-pose-angle (:theta (get-current-base-state-tf nh))
	init-odom-angle (quaternion->angle (:orientation (get-current-base-odom nh)))
	angle (+ init-odom-angle (- angle init-pose-angle))]
;    (println angle)
   (move-base-unsafe nh 
    (fn [init-pose current-pose]
      (let [ac (quaternion->angle (:orientation current-pose))
	    norm-diff (double (norm-angle (- angle ac)))]
;	(println norm-diff)
	{:angular {:z (if (> (Math/abs norm-diff) 0.25) (* (Math/signum norm-diff) 0.5) (* norm-diff 2))}}))
    (fn [init-pose current-pose]
      (let [ac (quaternion->angle (:orientation current-pose))
	    norm-diff (double (norm-angle (- angle ac)))]
	(< (Math/abs norm-diff) 0.03))))))


(defn move-base-precise [nh state]
  "Use move-base to get approximately to state, then unsafely servo to correct position."
;  (println "Trying to move precisely to" state)
  (when (= :success (move-base-to-pose-stamped nh (base-state->pose-stamped state)))
    (let [cbs (get-current-base-state nh)]
;    (println "Move base got us to" (get-current-base-state nh))
     (let [{:keys [x y theta]} state]
      (when (> (Math/abs (double (- theta (:theta cbs)))) 0.05) 
	(spin-base-to nh theta)
	(Thread/sleep 300))
      (let [[x y _] (transform-point-tf nh "/map" "/base_link" [x y 0])]
        (when (> (Math/abs (double x)) 0.02) (move-base-rel nh :x x 0.7 2.0))
        (when (> (Math/abs (double y)) 0.02) (move-base-rel nh :y y 1.0 2.0)))))
;    (println "Servoing got us to" (get-current-base-state nh))
    :success))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; Future base planning using navfn ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn base-state->disc [state res minc maxc]
  (let [[minx miny] minc [maxx maxy] maxc]
    (assert (<= minx (:x state) maxx))
    (assert (<= miny (:y state) maxy))
    (make-robot-base-state (+ 0.5 (int (/ (- (:x state) minx) res))) 
			   (+ 0.5 (int (/ (- (:y state) miny) res))) (:theta state))))

(defn base-state->cont [state res minc maxc]
  (let [[minx miny] minc]
    (make-robot-base-state (+ minx (* res (:x state))) 
			   (+ miny (* res (:y state))) (:theta state))))

; Assume costmap does not change.
(def *last-window* (atom nil))
(defn plan-base-motion
  [#^NodeHandle nh world initial-base-state final-base-state window]
  (let [res         (world-2d-res world) 
	[minc maxc] window
	slop        (map #(mod (- %2 (+ %1 (/ res 2))) res) minc [(:x final-base-state) (:y final-base-state)]) 
	minc        (map + minc slop)]
;    (println slop minc)
    (when-not (= [nh window] @*last-window*) ; Assume costmap is static.
      (println "Setting costmap")
      (call-srv  nh "/navfn_node/set_costmap" 
		(map-msg (world->costmap world minc maxc)))
      (reset! *last-window* [nh window]))
    (let [result 
	  (call-srv-cached nh "/navfn_node/make_plan" 
		    (map-msg {:class MakeNavPlan$Request
			:start (base-state->pose-stamped (base-state->disc initial-base-state res minc maxc))
			:goal  (base-state->pose-stamped (base-state->disc final-base-state res minc maxc))}))]
      (if (= 1 (:plan_found result))
;	(println result)
	(for [ps (:path result)]
	  (base-state->cont (pose->base-state ps) res minc maxc))
	(println "Failed to find base plan.")))))












;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;          Miscellanea         ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn map->base-link-transform [base]
  {:class Pose 
   :position    {:x (:x base) :y (:y base) :z 0.051}
   :orientation (axis-angle->quaternion-msg [0 0 1] (:theta base))})

(defn get-base-link->torso-lift-link-transform [torso-height]
  {:class Pose
   :position {:x -0.05, :y 0.0, :z (+ 0.7397 torso-height)}
   :orientation {:class Quaternion :x 0.0, :y 0.0, :z 0.0, :w 1.0}})

(defn map-pose->tll-pose-stamped [map-pose robot]
  {:class PoseStamped
   :header {:frame_id "/torso_lift_link"}
   :pose 
   (untransform-pose 
    (untransform-pose map-pose (map->base-link-transform (:base robot)))
    (get-base-link->torso-lift-link-transform (:height (:torso robot))))})


(comment

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


(defn get-trash-point [nh]
  (let [p (get-single-message-cached nh "/trash_can" (PointStamped.))]
    (transform-point nh (:frame_id (:header p)) "/base_link" (decode-point (:point p)))))

(defn servo-to-trash [nh]
  (spin-base-to-bar nh)
  (Thread/sleep 1000)
  (let [[x y] (get-trash-point nh)]
    (do (assert (< (Math/abs (double (- x 0.75))) 0.3))
	(move-base-rel nh :vx (- x 0.75)))))


(def *base-poses*
 {"bar1"     [6.437874062648721 11.352025609433628 4.669874589982046]
  "bar2"     [5.661619892642673 11.37858467149445 4.668634133660416]
  "bar3"     [4.804873093623918 11.504700687986952 4.569583493240115]
;  "bottle1"  [6.409466889875168 11.530285568135294 4.710902006993992]
;  "bottle2"  [6.209466889875168 11.530285568135294 4.710902006993992]
;  "bottle3"  [5.809466889875168 11.530285568135294 4.710902006993992]
;  "bottle4"  [5.609466889875168 11.530285568135294 4.710902006993992]
;  "bottle5"  [4.909466889875168 11.530285568135294 4.710902006993992]
;  "bottle6"  [4.786408482748747 11.540439761096412 4.753068777678795]
  "sink"     [9.775719015305087 7.97835357846113 4.7050955900786775]
             ;[9.925816301291352 8.226765986011085 4.7293563029386245]
  "trash"    [3.5361214867946433 11.34070696450406 4.693141702363712]
      ;[3.4471729012735567 11.465790341533662 4.748530929654799] ;fix
  "view-bar"         []
  "view-big-table"   []
  "view-small-table" [3.3843519644305093 13.019782651099014 1.4314826658466109] ;fix []
  "view-counter"     []
  "view-people"      []
  })


(def *big-table* [[5.50 8.11] [12.6 13.9] 0.75])

; backwards ...
(def *sim-table* [[23.94 26.94] [27.3 28.8] 0.75])
(def *sim-cup* [25.65 28.50])

 )

