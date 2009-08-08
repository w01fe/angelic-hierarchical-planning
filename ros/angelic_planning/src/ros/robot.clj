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



(ns ros.robot
  (:use   clojure.xml ros.ros ros.actions ros.world ros.geometry)
    (:require [edu.berkeley.ai.util :as util])
	  )
  
(set! *warn-on-reflection* true)

(import-ros)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Msgs, Helpers, Etc ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmsgs  [std_msgs Float64]
	  [geometry_msgs PointStamped PoseStamped PoseWithRatesStamped
	    PoseWithCovariance]
	  [robot_msgs PoseDot]
	  [nav_robot_actions MoveBaseState]
	  [motion_planning_msgs 
	   JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath]
	  [manipulation_msgs JointTraj IKRequest]
	  [move_arm MoveArmGoal MoveArmState]
	  [pr2_robot_actions  ActuateGripperState]
	  [mechanism_msgs    MechanismState]
	  )

(defsrvs  [motion_planning_msgs GetMotionPlan]
          [pr2_mechanism_controllers TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [manipulation_srvs    IKService ]
	  [tf_node              TransformPoint TransformPose]
	  [navfn                SetCostmap MakeNavPlan]
	  [fk_node              ForwardKinematics]
	  )



(defn string->input-stream [#^String s] 
 (java.io.ByteArrayInputStream. (.getBytes s "UTF-8")))

(defonce *robot-xml* nil)
(defonce *robot-joint-limits* nil)

(defn get-robot-xml []
  (def *robot-xml* 
       (parse (with-node-handle [nh] 
		(java.io.ByteArrayInputStream. 
		 (.getBytes (.getStringParam nh "/robot_description") "UTF-8")))))
  (def *robot-joint-limits*
       (into {}
	 (for [joint (:content *robot-xml*)
	       :when (and (= (:tag joint) :joint)
			  (every? (or (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) {})
				  [:min :max]))]
	   [(:name (:attrs joint))
	    (vec (map read-string
		   (map (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) [:min :max])))])))
  )


(defn get-current-mechanism-state [#^NodeHandle nh]
  (get-single-message nh "/mechanism_state" (MechanismState.)))

(def *tll-header* {:frame_id "/torso_lift_link"})
(def *bl-header*  {:frame_id "/base_link"})
(def *map-header* {:frame_id "/map"})



(defmulti get-joint-map :class)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *current-base-pose* (atom nil))
(def *base-pose-sub* (atom nil))

(defstruct robot-base-state    :class :x :y :theta)

(defn make-robot-base-state [x y theta]
  (struct robot-base-state ::BaseState x y theta))

(defmethod get-joint-map ::BaseState [obj]
  {"base_joint" [(:x obj) (:y obj) (:theta obj)]})

(defn pose-stamped->base-state [pose-stamped]
  (assert (#{"map" "/map"} (:frame_id (:header pose-stamped))))
  (let [pose (condp = (:class pose-stamped)
	       PoseWithCovariance   (:pose pose-stamped)
	       PoseStamped          (:pose pose-stamped)
	       PoseWithRatesStamped (:pose (:pose_with_rates pose-stamped)))]
    (make-robot-base-state
     (:x (:position pose))
     (:y (:position pose))
     (quaternion->angle (:orientation pose)))))

(defn base-state->pose-stamped [base-state]
  {:class PoseStamped
   :header {:frame_id "/map"}
   :pose   {:position {:x (:x base-state) :y (:y base-state) :z 0}
	    :orientation (angle->quaternion (:theta base-state))}})


;(defn get-current-base-pose [#^NodeHandle nh]
;  (get-single-message nh "/base_pose_ground_truth" (PoseWithRatesStamped.)))

(let [mem (atom {})]
  (def get-current-base-pose 
     (fn [#^NodeHandle nh]
       (let [a 
	     (or (@mem nh)
		 (let [a (atom nil)]
		   (.subscribe nh "/amcl_pose" (PoseWithCovariance.)
				      (sub-cb [m] (reset! a m)) 1)
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
		   (.subscribe nh "/robot_pose_ekf/odom_combined" 
			       (PoseWithCovariance.)
			       (sub-cb [m] (reset! a m)) 1)
		   (swap! mem assoc nh a)
		   a))]
	 (.spinOnce nh)
	 (while (not @a) (.spinOnce nh))
	 @a))))

(defn get-current-base-state [#^NodeHandle nh]
  (pose-stamped->base-state (get-current-base-pose nh)))



 
(defn move-base-to-pose-stamped 
  "Moves the base to the given pose-stamped, by invoking move_base."
  ([#^NodeHandle nh pose]
     (run-action nh "/move_base" (map-msg pose) (MoveBaseState.))))

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
		       

(defn move-base-unsafe 
  "Custom interface for moving base directly, without move_base."
  [#^NodeHandle nh command-fn goal-fn]
  (let [pub (.advertise nh "/cmd_vel" (PoseDot.) 1)]
    (let [init-pose (:pose (get-current-base-odom nh))
	  init-pos (:position init-pose)
	  zero     {:vx 0 :vy 0 :vz 0}]
      (loop []
	(let [current-pose (:pose (get-current-base-odom nh))]
  	 (when (not (goal-fn init-pose current-pose))
	  (.publish pub (map-msg PoseDot (update-in 
					  (update-in 
					   (command-fn init-pose current-pose)
					   [:vel] #(merge zero %))
					   [:ang_vel] #(merge zero %))))
	  (Thread/sleep 100)
	  (recur))))
      (.publish pub (map-msg PoseDot {:vel zero :ang_vel zero}))
      (println "Stopping: traveled" (point-distance init-pos (:position (:pose (get-current-base-odom nh)))))
;      (Thread/sleep 4000)
;      (println "Stopping: traveled" (point-distance init-pos (:position (:pose (get-current-base-odom nh))))))
      )
    (.shutdown pub)))


(defn move-base-rel
  "Directly moves using base controllers (unsafe), without invoking planning"
  [#^NodeHandle nh coord distance]
  (assert (#{:vx :vy} coord))
  (let [distance (double distance)
	dir (Math/signum distance)
	distance (Math/abs distance)]
   (move-base-unsafe nh
    (fn [init-pose current-pose]
      (let [dist (- distance (point-distance (:position init-pose) (:position current-pose)))]
	(println "commanding" (* dir (if (> dist 0.1) 0.2 (* dist 3))))
	{:vel {coord (* dir (if (> dist 0.1) 0.2 (* dist 3)))}}))
    (fn [init-pose current-pose]
      (let [dist (- distance (point-distance (:position init-pose) (:position current-pose)))]
	(< (Math/abs (double dist)) 0.005))))))

(defn norm-angle [a]
  (cond (> a Math/PI) (- a (* 2 Math/PI))
	(< a (- Math/PI)) (+ a (* 2 Math/PI))
	:else a))

(defn spin-base
  "Spins base at a specified vecocity (pos = ccw) for a specified time."
  [#^NodeHandle nh vel secs]
  (let [pub (.advertise nh "/cmd_vel" (PoseDot.) 1)
	sw  (util/start-stopwatch)
	msg (map-msg PoseDot {:vel {:vx 0 :vy 0 :vz 0}
			      :ang_vel {:vx 0 :vy 0 :vz vel}})]
    (loop []
      (.publish pub msg)
      (when (util/within-time-limit? sw secs)
	(Thread/sleep 100) 
	(recur)))
    (.shutdown pub)))

;; TODO: fix to use pose info
;; TODO: fix normalization
;(spin-base-to nh (- (* 1.5 (Math/PI)) 0.15))
(defn spin-base-to
  "Spins base to a desired angle, with no collision checking."
  [#^NodeHandle nh angle]
  (move-base-unsafe nh 
    (fn [init-pose current-pose]
      (let [ac (quaternion->angle (:orientation current-pose))
	    norm-diff (double (norm-angle (- angle ac)))]
	{:ang_vel {:vz (if (> (Math/abs norm-diff) 0.1) 0.5 (* norm-diff 4))}}))
    (fn [init-pose current-pose]
      (let [ac (quaternion->angle (:orientation current-pose))
	    norm-diff (double (norm-angle (- angle ac)))]
	(< (Math/abs norm-diff) 0.05)))))


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
	  (base-state->cont (pose-stamped->base-state ps) res minc maxc))
	(println "Failed to find base plan.")))))

;(defn motion-plan->

;; TODO: interpolate orientation.


(defn map->base-link-transform [base]
  {:class Pose 
   :position    {:x (:x base) :y (:y base) :z 0.051}
   :orientation (axis-angle->quaternion-msg [0 0 1] (:theta base))})

(def *base-link->torso-lift-link-transform*
     {:class Pose
      :position {:x -0.05, :y 0.0, :z 0.7448695339012872}
      :orientation {:class Quaternion :x 0.0, :y 0.0, :z 0.0, :w 1.0}})

(defn map-pose->tll-pose-stamped [map-pose base]
  {:class PoseStamped
   :header *tll-header*
   :pose 
   (untransform-pose 
    (untransform-pose map-pose (map->base-link-transform base))
    *base-link->torso-lift-link-transform*)})






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Gripper ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::LeftGripperState ::GripperState)
(derive ::LeftGripperState ::Left)
(derive ::RightGripperState ::GripperState)
(derive ::RightGripperState ::Right)

(defstruct robot-gripper-state :class :open? :force :holding)

(defn make-robot-gripper-state 
  ([right? open?]
     (make-robot-gripper-state right? open? 100 false))
  ([right? open? force holding]
     (when open? (assert (not holding)))
     (struct robot-gripper-state (if right? ::RightGripperState ::LeftGripperState) 
	     open? (Math/abs (double force)) holding)))

(def *gripper-mul* 5.55) ; Multiplier for weird gripper joints

(defmethod get-joint-map ::GripperState [obj]
  (let [sep (if (:open? obj) 0.0885 0.0)
	cr (if (isa? (:class obj) ::Right) "r" "l")]
    (into {} (concat [[(str cr "_gripper_joint") sep]
		      [(str cr "_gripper_float_joint") 0.0]]
		     (for [finger ["l" "r"]
			   joint ["joint" "tip_joint"]]
		       [(str cr "_gripper_" finger "_finger_" joint) (* *gripper-mul* sep)])))))

(defn get-current-gripper-state [nh right?]
  (make-robot-gripper-state right? 
    (>
     (:position (first (filter #(= (:name %) (str (if right? "r" "l") "_gripper_joint"))
			      (:joint_states (get-current-mechanism-state nh)))))
     0.06)
    ))

(defn apply-gripper-force [#^NodeHandle nh right? force]
  (put-single-message nh (str "/actuate_gripper_" (if right? "right" "left") "_arm/activate")
		      (map-msg Float64 {:data force}) 1))

(defn move-gripper-to-state 
  ([nh gs]
     (apply-gripper-force nh (isa? (:class gs) ::Right) (* (:force gs) (if (:open? gs) 1 -1)))))


; Bottles - 45 (everything)


(comment 
(defn open [] (move-gripper-to-state nh (make-robot-gripper-state nh true)))
(defn close [] (move-gripper-to-state nh (make-robot-gripper-state nh false 0.45 nil)))
(defn fw [x] (move-base-rel nh :vx x))
(defn r  [x] (move-base-rel nh :vy x))
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arms ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(derive ::LeftArmState ::ArmState)
(derive ::LeftArmState ::Left)
(derive ::RightArmState ::ArmState)
(derive ::RightArmState ::Right)

(defstruct robot-arm-state     :class :tucked? :joint-angle-map) ;:gripper-state

(defn make-robot-arm-state [right? tucked? joint-angle-map]
  (struct robot-arm-state (if right? ::RightArmState ::LeftArmState) tucked? joint-angle-map))

(defmethod get-joint-map ::ArmState [obj] (:joint-angle-map obj))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Get, move to state ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Known trajectories, etc. ;;;


(def *arm-joints*
  ["shoulder_pan_joint" "shoulder_lift_joint" "upper_arm_roll_joint" 
   "elbow_flex_joint" "forearm_roll_joint" "wrist_flex_joint" "wrist_roll_joint"])
(def *arm-joint-wraps* [false false false false true false true])

(def *larm-joints* (map #(str "l_" %) *arm-joints*))
(def *rarm-joints* (map #(str "r_" %) *arm-joints*))



(def *larm-joint-states*
     {"up"                [1.033456 -0.218231 0.115697 -1.082723 -2.929992 0.107283 -1.695491]
      "tucked"            [-0.000020 0.899529 1.569952 -1.550905 0.000192 0.100453 -0.000417]})

(def *rarm-joint-states*
     {"up"                [-1.060668 -0.336501 -0.099800 -0.974440 3.106211 0.139013 2.735894]
      "tucked"            [-0.000186 1.286251 -1.569942 -1.570996 -0.000091 0.101947 0.000223]
      "home"              [0.39146 0.770561 -0.593027 -1.99714 0.742525 1.60109 2.63896]
      "grasp_bar"         [-0.112613 -0.215548 -2.5479 0.002441 -0.14698 0.263452 2.53254]
      "grasp_bar_low"     [-0.0888183 -0.150892 -0.134794 -0.0605298 2.96289 0.268543 -3.0757]
      "grasp_big_table"   [-0.00313992 -0.0117858 -0.105762 -0.0776116 3.08055 0.10099 -3.01161]
      "grasp_small_table" [-0.250178 0.0616681 -0.109955 -0.118579 3.04295 0.184788 -3.0405]
      "grasp_counter"     [-0.356016 -0.188573 -0.0260828 -0.719335 -3.05293 0.870881 -2.97632]
      "drop"              [0.00685727 0.412504 -0.0828579 -1.51335 -3.08632 1.05988 -2.91744]
      })

(defn arm-joint-state 
  ([right? name]
     (arm-joint-state right? name false))
  ([right? name tucked?]
     (make-robot-arm-state right? tucked? 
      (into {} (map vector 
		    (if right? *rarm-joints* *larm-joints*)
		    (safe-get* (if right? *rarm-joint-states* *larm-joint-states*) name))))))

(defn arm-l2-distance [j1 j2]
  (Math/sqrt (double (apply + (map #(* % %) 
    (for [[v1 v2 roll?] (map vector j1 j2 *arm-joint-wraps*)]
      (let [diff (Math/abs (double (- v1 v2)))]
	(if roll? (if (> diff Math/PI) (- (* 2 Math/PI) diff) diff) diff))))))))


(defn interpolate-arm-joint [v1 v2 w wrap?]
  (let [dist (double (- v2 v1))]
    (if (or (not wrap?) (< (Math/abs dist) Math/PI))
        (+ v1 (* dist w))
      (norm-angle (- v1 (* (- (* 2 Math/PI) dist) w))))))

(defn interpolate-arm-joints [j1 j2 w]
  (map (fn [v1 v2 wrap?] (interpolate-arm-joint v1 v2 w wrap?)) j1 j2 *arm-joint-wraps*))

;;; Using known states ;;;


(defn get-current-arm-state-msg [nh right?]
  (call-srv-cached nh (str "/" (if right? "r" "l") 
		    "_arm_joint_waypoint_controller/TrajectoryQuery" )
	    (map-msg TrajectoryQuery$Request {:trajectoryid (TrajectoryQuery$Request/Query_Joint_Names)})))

(defn get-current-arm-state [nh right?]
  (let [{:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)]
    (make-robot-arm-state right? false (apply array-map (interleave jointnames jointpositions)))))


(defn make-joint-trajectory [init-joints final-joints]
  (assert (= (set (keys init-joints)) (set (keys final-joints))))
  (let [ks (keys init-joints)]
    {:class JointTraj :names ks 
     :points (map (fn [m t] {:positions (map m ks) :time t}) [init-joints final-joints] [0 0.2])}))




 ;; TODO: handle wraparound
(defn make-smooth-joint-trajectory [init-joints final-joints step-l2 step-time]
  (assert (= (set (keys init-joints)) (set (keys final-joints))))
  (let [ks (keys init-joints)
	j1 (map init-joints ks)
	j2 (map final-joints ks)
	jd (map - j2 j1)
	total-dist (arm-l2-distance j1 j2)
	steps (inc (int (/ total-dist step-l2)))
	step-dist (/ total-dist steps)
	step-time (* step-time (/ step-dist step-l2))]
    {:class JointTraj :names ks 
     :points 
       (for [t (range (inc steps))]
	 {:positions (interpolate-arm-joints j1 j2 (/ t steps))
	    ;(map + j1 (map #(* % (/ t steps)) jd)) 
	  :time (* step-time t)})}))
   

(defn start-trajectory [#^NodeHandle nh srv-prefix traj]
;  (println traj)
;  (throw (RuntimeException.))
  (safe-get*
   (call-srv-cached nh (str srv-prefix "/TrajectoryStart")
      (map-msg TrajectoryStart$Request {:traj traj :hastiming 0 :requesttiming 0}))
   :trajectoryid))

(defonce *good-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Done])))

(defonce *bad-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Deleted
		 TrajectoryQuery$Response/State_Failed
		 TrajectoryQuery$Response/State_Canceled
;		 TrajectoryQuery$Response/State_Does_Not_Exist
		 ])))

(defn wait-for-trajectory 
  "Wait for a given trajectory, at most max-seconds.  Returns false
   for success, and an error code (Response code, or :timeout) on failure."
  ([#^NodeHandle nh srv-prefix traj-id]
     (wait-for-trajectory nh srv-prefix traj-id 1000))
  ([#^NodeHandle nh srv-prefix traj-id max-seconds]
  (print "Waiting for trajectory" traj-id "...")
  (let [sw (util/start-stopwatch)]
   (loop []
     (let [outcome (int (:done 
		       (call-srv-cached nh (str srv-prefix "/TrajectoryQuery")
				      (map-msg TrajectoryQuery$Request
					       {:trajectoryid traj-id}))))]
      (cond (*good-traj-outcomes* outcome) (do (println outcome) false)
	    (*bad-traj-outcomes* outcome) (do (println outcome) outcome)
	    :else (if (util/within-time-limit? sw max-seconds) 
	  	      (do (print outcome)  
			  (Thread/sleep 100)
		  	  (recur))
		    (do (println "Timeout, interruping ...")
			(call-srv-cached nh (str srv-prefix "/TrajectoryCancel")
					 (map-msg TrajectoryCancel$Request {:trajectoryid traj-id}))
			:timeout
		      ))))))))


(defn execute-arm-trajectory [#^NodeHandle nh traj wait-secs]
  (let [right? (condp = (first (first (:names traj))) \r true \l false)
	srv-prefix (str "/" (if right? "r" "l") "_arm_joint_waypoint_controller")
	id (start-trajectory nh srv-prefix traj)]
    (or (and (not wait-secs) [srv-prefix id])
	(wait-for-trajectory nh srv-prefix id wait-secs))))

(defn move-arm-directly-to-state 
  ([#^NodeHandle nh arm-state]
     (move-arm-directly-to-state nh arm-state 10))
  ([#^NodeHandle nh arm-state wait-secs]
     (execute-arm-trajectory nh 
       (make-smooth-joint-trajectory (:joint-angle-map (get-current-arm-state nh 
						        (isa? (:class arm-state) ::Right))) 
				     (:joint-angle-map arm-state)
				      0.2 0.01)
       wait-secs)))

(defn read-path-file [f] (map #(read-string (str "[" % "]")) (util/read-lines f)))

(def *drop-traj* (read-path-file "/u/isucan/paths/discard"))

(defn encode-arm-trajectory [right? traj timestep]
  {:class JointTraj :names (if right? *rarm-joints* *larm-joints*)
   :points (for [[t joints] (util/indexed traj)] {:positions joints :time (* t timestep)})})

(defn encode-normalized-arm-trajectory [right? traj speed]
  (let [pairs     (partition 2 1 traj)
	distances (map (fn [[x y]] (arm-l2-distance x y)) pairs)
	path-distances (util/reductions + distances)]
;    (println distances path-distances)
    {:class JointTraj :names (if right? *rarm-joints* *larm-joints*)
     :points (cons {:positions (first traj) :time 0}
		   (for [[[prev cur] dist path-dist] (map vector pairs distances path-distances) 
			 :when (> dist 0.00001)]
		     {:positions cur :time (/ path-dist speed)}))}))


;TODO: handle wraparound! (also above!)
#_(defn encode-smoothed-arm-trajectory [right? traj res speed]
  (let [norm (encode-normalized-arm-trajectory right? traj speed)]
    (assoc-in norm [:points]
      (fn [points]
	(cons (first points)
	  (rest 
	   (loop [i -1 cur-sum 0 cur-dist res next-sum 0 next-dist 0 traj traj traj-out []]
	     (let [[first-traj & rest-traj] traj]
	       (if (empty? rest-traj) (conj traj-out first-traj)
		 (let [second-traj (first rest-traj)]
		   (let [dist (arm-l2-distance first-traj second-traj)]
		     (assert (< (+ next-dist dist) (* 2 res)))
		     (if (> (+ cur-dist dist) (* 2 res))
		         (recur (inc i) 
				(map + next-sum ...) (+ next-dist dist)
				... ...
				rest-traj
				(conj traj-out ...))
		       (recur i
			      (map + cur-sum ...) (+ cur-dist dist)
			      (map + next-sum ...) (+ next-dist dist)
			      rest-traj traj-out)))))))))))))

    
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tuck and untuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(defn throw-arms [#^NodeHandle nh]
  (doseq [[p id] (doall (for [r? [false true]]
		    (move-arm-directly-to-state nh (arm-joint-state r? "up") false)))]
    (wait-for-trajectory nh p id))) 


(defn tuck-arms [#^NodeHandle nh]
  (doseq [[p id] [(move-arm-directly-to-state nh (arm-joint-state true "tucked" true) false)
		(do (Thread/sleep 1000)
		    (move-arm-directly-to-state nh (arm-joint-state false "tucked" true) false))]]
    (wait-for-trajectory nh p id)))
  

(defn throw-and-tuck-arms [#^NodeHandle nh]
  (throw-arms nh) (tuck-arms nh))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Kinematics ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: random joint configs.
; TODO: not very useful without collision checking of IK solutions.
; Pose is for something like, but not exactly, palm link.
(defn inverse-kinematics
  "Returns a final joint map (possibly in collision) or nil for failure.
   Pose-stamped must be a pose of a *_gripper_palm_link, in the torso_lift_link frame."
  [#^NodeHandle nh right? pose-stamped init-joint-map]
  (assert (= (:frame_id (:header pose-stamped)) "/torso_lift_link"))
  (let [init-joints (seq init-joint-map)]
;    (map-msg 
;		     {:class IKService$Request
;		      :data {:joint_names (map first init-joints)
;			     :positions   (map second init-joints)
;			     :pose_stamped pose-stamped}})))
    (try 
     (into {} (map vector (map first init-joints) 
       (:solution (call-srv-cached nh (str "/pr2_ik_" (if right? "right" "left") "_arm/ik_service")  
		    (map-msg 
		     {:class IKService$Request
		      :data {:joint_names (map first init-joints)
			     :positions   (map second init-joints)
			     :pose_stamped pose-stamped}})))))
     (catch RosException e
       nil
       ))))




(defn make-kinematic-joint [[joint-name joint-position]]
  {:class KinematicJoint :header (assoc *map-header* :stamp (.subtract (.now *ros*) (Duration. 0.1)))
   :joint_name joint-name :value (if (coll? joint-position) (vec (map double joint-position)) [(double joint-position)])})

(def *fk-z-offset* 0.09412233491155875)

(defn forward-kinematics
  "Returns a lazy seq [in-collision? poses], where poses is a map
   from link names to poses.  Assumes joints in map frame.
   If in_collision is to be accurate, must first publish a collision map
   to the appropriate topic in the fk_node.  Response is in base link."
 [#^NodeHandle nh joint-map]
   (let [res (call-srv-cached nh "/fk_node/forward_kinematics"
	      (map-msg {:class ForwardKinematics$Request
			:joints (map make-kinematic-joint joint-map)}))]
;     (println res)
     (assert (= (count (:link_names res)) (count (:link_poses res))))
    (cons (> (:in_collision res) 0)
	  (lazy-seq [(apply hash-map (interleave (:link_names res) 
						 (for [pose (:link_poses res)]
						   (update-in pose [:position :z] #(- % *fk-z-offset* )))))]))))




(defn robot-forward-kinematics
  "Like forward-kinematics, but takes a robot state and possibly world state,
   if a collision map is to be published."
 ([#^NodeHandle nh robot]
    (forward-kinematics nh (get-joint-map robot)))
 ([#^NodeHandle nh robot world]
    (put-single-message-cached nh "/fk_node/collision_map" 
      (map-msg (world->collision-map world)) )
    (robot-forward-kinematics nh robot)))



(def get-arm-joint-names 
    (memoize (fn [nh right?] 
	       (keys (:joint-angle-map (get-current-arm-state nh right?))))))

(defn random-arm-joint-map [nh right?]
  (when-not *robot-joint-limits* (get-robot-xml))
    (into {}
    (for [joint (get-arm-joint-names nh right?)
	  :let [limits (*robot-joint-limits* joint)]]
      [joint (rand-double 
	      (or limits
		 (do ;(println "Warning: no limits for joint" joint)
		     [0 (* 2 Math/PI)])))])))

(defn feasible-ik-pose? 
  "Is it physically possible to reach the given pose?  If no, we won't
   bother trying to call IK."
  [right? pose-stamped]
  (let [pos (pose-position (:pose pose-stamped))
	[x y z] pos]
     (println pos (l2-distance [0 0 0] pos))
    (cond (< x 0) 
            (println "Skipping IK; can't reach behind robot.")
	  (> (l2-distance [0 0 0] pos) 0.9)
	    (println "Skipping IK; can't reach more than 0.9 meters away.")
	  ; ...
          :else true)))

(defn safe-inverse-kinematics 
  "Find an IK solution respecting the collision space.  Pass
   world if you want its collision map published.
   Other initial joint configurations will be randomly generated."
  ([#^NodeHandle nh right? pose-stamped robot world random-retries]
     (safe-inverse-kinematics nh right? pose-stamped robot world random-retries false))
  ([#^NodeHandle nh right? pose-stamped robot world random-retries start-random?]
   (when (feasible-ik-pose? nh pose-stamped) ;; TODO: replace with opt desc.
     (when world
       (put-single-message-cached nh "/fk_node/collision_map" 
	 (map-msg (world->collision-map world))))
     (println "Sent map!")
     (let [all-joints (get-joint-map robot)]
      (loop [tries random-retries 
	    init-joints (if start-random? (random-arm-joint-map nh right?)
			    (:joint-angle-map ((if right? :rarm :larm) robot)))]
;       (println init-joints)
       (or (if-let [sol (time (inverse-kinematics nh right? pose-stamped init-joints))]
	     (let [collision (first (time (forward-kinematics nh (merge all-joints sol))))]
	       (println "Found IK solution ..."
			(if collision "" " not ") "in collision.") 
	       (when (not collision)
		 sol))
	     (println "Failed to find IK solution"))
	   (when (> tries 0)
;	     (println "IK failed; retrying with random initial joints.")
	     (recur (dec tries) (random-arm-joint-map nh right?)))))))))
	 
     


; (inverse-kinematics nh true {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.53 :y -0.02 :z -0.38} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 0.0 :w 1.0}}} (:joint-angle-map (get-current-arm-state nh true)))


;(defn move-arm-directly-to-pose [nh right? pose-stamped ]
;  (when-let [joints (compute-ik nh pose-stamped (get-arm-joints right?))]
;    (println joints)))
;    (move-arm-directly-to nh right? (into {} joints))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Arm Planning  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def *shared-arm-params*
     {:class KinematicSpaceParameters
      :contacts nil
      :distance_metric "L2Square" :planner_id      "" :contacts nil
      :volumeMin       {:header *map-header* :point {:x 0 :y 0 :z 0}}
      :volumeMax       {:header *map-header* :point {:x 0 :y 0 :z 0}}})
(def *larm-params* (assoc *shared-arm-params* :model_id "left_arm"))
(def *rarm-params* (assoc *shared-arm-params* :model_id "right_arm"))

(def *no-constraints* {:class KinematicConstraints :joint_constraint [] :pose_constraint []})

(def *joint-constraint-tolerance* 0.001)


(defn parse-joint-constraint [[name val]]
  (if (map? val) val
    (let [[value tol]
	  (cond (number? val) 
		  [(double val) *joint-constraint-tolerance*]
		(coll?   val) 
		  (let [[mn mx] val]
		    (assert (= (count val) 2))
		    [(/ (+ mn mx) 2.0) (/ (- mx mn) 2.0)])
		:else (throw (RuntimeException. "Unknown joint constraitn type.")))]
      {:class JointConstraint 
       :header *tll-header*
       :joint_name name
       :value          [value]
       :tolerance_above [tol]
       :tolerance_below [tol]})))

  

(defn encode-xyz-pose-constraint-type [x? y? z?]
  (+ (if x? PoseConstraint/POSITION_X 0)
     (if y? PoseConstraint/POSITION_Y 0)
     (if z? PoseConstraint/POSITION_Z 0)))

(defn encode-rpy-pose-constraint-type [r? p? y?]
  (+ (if r? PoseConstraint/ORIENTATION_R 0)
     (if p? PoseConstraint/ORIENTATION_P 0)
     (if y? PoseConstraint/ORIENTATION_Y 0)))


(defn encode-pose-constraint-type [[x? y? z?] [roll? pitch? yaw?]]
  (+ (encode-xyz-pose-constraint-type x? y? z?)
     (encode-rpy-pose-constraint-type roll? pitch? yaw?)))

; TODO: nice, abstract position, orientation representations.

(defn encode-pose-constraint 
  ([right? frame [x y z] [ax ay az] angle]
     (encode-pose-constraint right? frame [x y z] [ax ay az] angle [true true true] [true true true]))
  ([right? frame [x y z] [ax ay az] angle [x? y? z?] [roll? pitch? yaw?]]
     (assert (= frame "/map"))
   (let [tol {:class Point :x 0.001 :y 0.001 :z 0.001}]
  {:class PoseConstraint :class (encode-pose-constraint-type [x? y? z?] [roll? pitch? yaw?])
   :orientation_importance 0.5
   :position_tolerance_above tol :position_tolerance_below tol
   :orientation_tolerance_above tol :orientation_tolerance_below tol
   :link_name (str (if right? "r" "l") "_gripper_palm_link")
   :pose {:header {:frame_id frame}
	  :pose   {:position    {:x x :y y :z z}
		   :orientation (axis-angle->quaternion-msg [ax ay az] angle)}}})))
  
(def *upright-rgripper-constraint*
  (let [tolv 0.5
	tol {:x tolv :y tolv :z tolv}]
   {:joint_constraint nil
    :pose_constraint 
     [{:type (+ PoseConstraint/ORIENTATION_R PoseConstraint/ORIENTATION_P)
       :link_name "r_gripper_palm_link"
       :pose {:header *bl-header* :pose (make-pose [0 0 0] [0 0 0 1])}
       :orientation_importance 1.0
       :orientation_tolerance_above tol
       :orientation_tolerance_below tol
       :position_tolerance_above tol
       :position_tolerance_below tol}]}))
       

(defn plan-arm-motion
  "joint constraints are passed as map from name to either value,  
   which will use this tolerance, or interval, or joint_constraint map.
   pose constraints are lists of PoseConstraints maps -- no shortcuts for now.
   Init-joints should include base and torso, in general."
  ([#^NodeHandle nh right? world robot-state joint-constraints pose-constraints]
     (plan-arm-motion nh right? world robot-state joint-constraints pose-constraints *no-constraints*))
  ([#^NodeHandle nh right? world robot-state joint-constraints pose-constraints path-constraints]
  (println "Putting collision map")
  (put-single-message-cached nh "/collision_map_future" (map-msg (world->collision-map world)))
;  (println "\n\n\n\n\n\n\n\n" right?)
;  (println (doall (map make-kinematic-joint (get-joint-map robot-state))))
;  (println "\n\n\n")
;  (println pose-constraints)
    (println "Calling plan service")
  (call-srv-cached nh "/future_ompl_planning/plan_kinematic_path"
   (map-msg 
     {:class GetMotionPlan$Request :times 1 :allowed_time 0.5 :planner_id ""
      :params (if right? *rarm-params* *larm-params*)
      :start_state      (doall (map make-kinematic-joint (get-joint-map robot-state)))
      :path_constraints path-constraints
      :goal_constraints {:pose_constraint (vec pose-constraints)
			 :joint_constraint (vec (map parse-joint-constraint joint-constraints))}}))))


(defn describe-motion-plan [plan]
  (if (empty? (:states (:path plan)))
      (println "No plan was found")
    (println 
     (str ;(if (:unsafe plan) "unsafe ") 
	  (if (> (:approximate plan) 0) (str "approximate, with distance " (:distance plan) " "))
	  "plan with " (count (:states (:path plan))) " states, time " (last (:times (:path plan)))
	  " found."))))


(defn move-arm-to-state 
  "Actually move arm to state using move_arm action, with replanning, synchronously"
  [#^NodeHandle nh arm-state]
  (run-action nh (str "/move_" (if (isa? (:class arm-state) ::Right) "right" "left") "_arm") 
    (map-msg {:class MoveArmGoal 
	      :contacts nil
	      :path_constraints *no-constraints*
	      :goal_constraints {:pose_constraint  []
				 :joint_constraint (vec (map parse-joint-constraint 
							     (:joint-angle-map arm-state)))}})
    (MoveArmState.)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Torso ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct robot-torso-state   :class :height)

(defn make-robot-torso-state [height]
  (struct robot-torso-state ::TorsoState height))

(defmethod get-joint-map ::TorsoState [obj]
  {"torso_lift_joint" (:height obj)})

(defn get-current-torso-state [#^NodeHandle nh]
  (make-robot-torso-state 
    (:position 
     (first (filter #(= (:name %) "torso_lift_joint") 
	      (:joint_states (get-current-mechanism-state nh)))))))

(defn set-torso-position [#^NodeHandle nh pos]
  (put-single-message nh "/torso_lift_controller/set_command" 
		      (map-msg {:class Float64 :data pos}) 1))

; Todo: make synchronous?
(defn move-torso-to-state [nh state]
  (set-torso-position nh (:height state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Robot ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct robot-state         :class :base :torso :larm :rarm :lgripper :rgripper)
(defn make-robot-state [base torso larm rarm lgripper rgripper]
  (struct robot-state ::RobotState base torso larm rarm lgripper rgripper))

(defn get-current-robot-state [nh]
  (make-robot-state 
   (get-current-base-state nh)
   (get-current-torso-state nh)
   (get-current-arm-state nh false)
   (get-current-arm-state nh true)
   (get-current-gripper-state nh false)
   (get-current-gripper-state nh true)))
  
(defmethod get-joint-map ::RobotState [obj]
  (apply merge (map #(get-joint-map (% obj)) [:base :torso :larm :rarm :lgripper :rgripper])))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Abstract States ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(set! *warn-on-reflection* false)



; (do (use 'ros.ros 'ros.world 'ros.geometry 'ros.robot 'ros.robot-actions 'ros.robot-hierarchy :reload) (import-ros) (import-all-msgs-and-srvs))
; (def nh (make-node-handle))

; (call-srv "/tf_node/transform_point" (map-msg {:class TransformPoint$Request :target_frame "/map" :pin {:class PointStamped :header {:class Header :frame_id "/odom" :stamp (.subtract (.now *ros*) (Duration. 0.1))} :point {:class Point :x 0 :y 0 :z 0}} :fixed_frame "" :target_time (Time.)}))

; (count (:times (:path (plan-arm-motion nh true (get-initial-world 0.1 0.1 0) (assoc (get-current-robot-state nh)  :base (make-robot-base-state 8 9 0) :torso (make-robot-torso-state 0.2)) (:joint-angle-map *rarm-tucked-state*) nil))))






;(defn move-base-to-pose-stamped 
;  "Moves the base to the given pose-stamped, by invoking move_base.
;   If wait-for-dist? is non-nil, blocks until the robot is within this distance of the goal."
;  ([nh pose]
;     (move-base-to-pose-stamped nh pose nil))
;  ([#^NodeHandle nh pose wait-for-dist?]
;     (put-single-message nh "/move_base/activate" (map-msg pose) 1) 		      
;     (when wait-for-dist? (println "wait...")
;	   (while (> (pose-distance pose (:pos (get-current-base-pose nh)) 1.0) wait-for-dist?)
;	     (Thread/sleep 100)))))

;(defn move-base-to-state
;  "Like move-base-to-pose-stamped, but takes a robot-base-state"
;  ([nh state]
;     (move-base-to-state nh state nil))
;  ([nh state wait-for-dist?]
;     (move-base-to-pose-stamped nh (base-state->pose-stamped state) wait-for-dist?)))
