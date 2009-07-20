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
  (:use   clojure.xml ros.ros ros.actions ros.world)
	  )
  
(set! *warn-on-reflection* true)

(import-ros)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Msgs, Helpers, Etc ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def nh (.createNodeHandle *ros*))

(defmsgs [ros.pkg
	  [roslib.msg Header]
	  [std_msgs.msg ColorRGBA Float64]
	  [robot_msgs.msg
	     OccGrid MapMetaData 
	     Point PointStamped Vector3 Quaternion
	     Velocity AngularVelocity Acceleration AngularAcceleration 
	     Pose PoseDot PoseDDot PoseStamped PoseWithRatesStamped]
	  [robot_actions.msg ActionStatus] 
	  [nav_robot_actions.msg MoveBaseState]
	  [motion_planning_msgs.msg 
	   JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath ]
	  [manipulation_msgs.msg JointTrajPoint JointTraj IKRequest ]
;	 [topological_map.msg Cell Connector ConnectorEdge MapRegion]
	  [visualization_msgs.msg Polyline]
	  [pr2_robot_actions.msg MoveArmGoal MoveArmState]
	  [mechanism_msgs.msg JointState ActuatorState MechanismState]
	  ])



(defsrvs [ros.pkg
	  [pr2_mechanism_controllers.srv TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [motion_planning_srvs.srv MotionPlan]
	  [manipulation_srvs.srv    IKService]
	  [tf_node.srv              TransformPoint TransformPose]
	  [navfn.srv SetCostmap MakeNavPlan]
;	  [robot_srvs.srv StaticMap]
;	  [topological_map.srv GetTopologicalMap]
	  ])



(defn string->input-stream [#^String s] 
 (java.io.ByteArrayInputStream. (.getBytes s "UTF-8")))

(defonce *robot-xml* nil)
(defonce *robot-joint-limits* nil)

(defn get-robot-xml []
  (def *robot-xml* 
       (parse (with-node-handle [nh] 
		(java.io.ByteArrayInputStream. 
		 (.getBytes (.getStringParam nh "/robotdesc/pr2") "UTF-8")))))
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

(defn l2-distance [v1 v2]
   (Math/sqrt (reduce + (map #(let [x (- (double %1) (double %2))] (* x x)) v1 v2))))


(defn angle->quaternion [rads]
  {:class Quaternion :x 0 :y 0 :z (Math/sin (double (/ rads 2))) 
   :w (Math/cos (double (/ rads 2)))})

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


(defmulti get-joint-map :type)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defstruct robot-base-state    :type :x :y :theta)

(defn make-robot-base-state [x y theta]
  (struct robot-base-state ::BaseState x y theta))

(defmethod get-joint-map ::BaseState [obj]
  {"base_joint" [(:x obj) (:y obj) (:theta obj)]})

(defn pose-stamped->base-state [pose-stamped]
  (assert (#{"map" "/map"} (:frame_id (:header pose-stamped))))
  (let [pose (condp = (:class pose-stamped)
	       PoseStamped          (:pose pose-stamped)
	       PoseWithRatesStamped (:pos pose-stamped))]
    (make-robot-base-state
     (:x (:position pose))
     (:y (:position pose))
     (quaternion->angle (:orientation pose)))))

(defn base-state->pose-stamped [base-state]
  {:class PoseStamped
   :header {:class Header :frame_id "/map"}
   :pose   {:class Pose
	    :position {:class Point :x (:x base-state) :y (:y base-state) :z 0}
	    :orientation (angle->quaternion (:theta base-state))}})


(defn get-current-base-pose [#^NodeHandle nh]
  (get-single-message nh "/base_pose_ground_truth" (PoseWithRatesStamped.)))

(defn get-current-base-state [#^NodeHandle nh]
  (pose-stamped->base-state (get-current-base-pose nh)))




(defn- point-distance [p1 p2]
  (let [vecs (map #(map % [:x :y :z]) [p1 p2])]
    (Math/sqrt (double (apply + (apply map #(* (- %1 %2) (- %1 %2)) vecs))))))

(defn- orientation-distance [o1 o2]
  (let [a  (* 2 (Math/acos (apply + (apply map * (map #(map % [:x :y :z :w]) [o1 o2])))))]
    (if (< a (Math/PI)) a (- (* 2 Math/PI) a))))

(defn- pose-distance [p1 p2 angle-wt]
  (let [pd (point-distance (:position p1) (:position p2))
	od (orientation-distance (:orientation p1) (:orientation p2))]
  ;  (println pd od)
    (+ pd (* angle-wt od)))) 


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

(defn move-base-to-pose-stamped 
  "Moves the base to the given pose-stamped, by invoking move_base.
   If wait-for-dist? is non-nil, blocks until the robot is within this distance of the goal."
  ([#^NodeHandle nh pose]
     (run-action nh "/move_base" (map-msg pose) (MoveBaseState.))))

(defn move-base-to-state
  "Like move-base-to-pose-stamped, but takes a robot-base-state"
  ([nh state]
     (move-base-to-pose-stamped nh (base-state->pose-stamped state))))



(defn move-forward 
  "Directly moves using base controllers, without invoking planning"
  [#^NodeHandle nh steps]
  (let [pub (.advertise nh "/cmd_vel" (PoseDot.) 1)] 
    (dotimes [_ (Math/abs (int steps))] 
      (Thread/sleep 100) 
      (.publish pub (map-msg {:class PoseDot :vel {:class Velocity :vx (* 0.5 (Math/signum (double steps)) 2) :vy 0 :vz 0} 
			      :ang_vel {:class AngularVelocity :vx 0 :vy 0 :vz 0}})))
    (.shutdown pub)))


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

(defn plan-base-motion
  [#^NodeHandle nh world initial-base-state final-base-state window]
  (let [res         (world-2d-res world) 
	[minc maxc] window
	slop        (map #(mod (- %2 (+ %1 (/ res 2))) res) minc [(:x final-base-state) (:y final-base-state)]) 
	minc        (map + minc slop)]
;    (println slop minc)
    (call-srv nh "/navfn_node/set_costmap" 
	      (map-msg (world->costmap world minc maxc)))
    (let [result 
	  (call-srv nh "/navfn_node/make_plan" 
		    (map-msg {:class MakeNavPlan$Request
			:start (base-state->pose-stamped (base-state->disc initial-base-state res minc maxc))
			:goal  (base-state->pose-stamped (base-state->disc final-base-state res minc maxc))}))]
      (when (= 1 (:plan_found result))
;	(println result)
	(for [ps (:path result)]
	  (base-state->cont (pose-stamped->base-state ps) res minc maxc))))))

;(defn motion-plan->

;; TODO: interpolate orientation.






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Gripper ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::LeftGripperState ::GripperState)
(derive ::LeftGripperState ::Left)
(derive ::RightGripperState ::GripperState)
(derive ::RightGripperState ::Right)

(defstruct robot-gripper-state :type :separation :holding)

(defn make-robot-gripper-state [right? sep holding]
  (struct robot-gripper-state (if right? ::RightGripperState ::LeftGripperState) sep holding))

(def *gripper-mul* 5.55) ; Multiplier for weird gripper joints

(defmethod get-joint-map ::GripperState [obj]
  (let [sep (:separation obj)
	cr (if (isa? (:type obj) ::Right) "r" "l")]
    (into {} (concat [[(str cr "_gripper_joint") sep]
		      [(str cr "_gripper_float_joint") 0.0]]
		     (for [finger ["l" "r"]
			   joint ["joint" "tip_joint"]]
		       [(str cr "_gripper_" finger "_finger_" joint) (* *gripper-mul* sep)])))))

(defn get-current-gripper-state [nh right?]
  (make-robot-gripper-state right? 
    (:position (first (filter #(= (:name %) (str (if right? "r" "l") "_gripper_joint"))
			      (:joint_states (get-current-mechanism-state nh)))))
    false))

(defn set-gripper-separation [#^NodeHandle nh right? sep]
  (put-single-message (str (if right? "r" "l") "_gripper_position_controller/set_command")
		      (map-msg {:class Float64 :data (double sep)})))

(defmulti move-gripper-to-state (fn [nh gs] (:type gs)))
(defmethod move-gripper-to-state ::Left [nh state] (set-gripper-separation nh false (:separation state))) 
(defmethod move-gripper-to-state ::Right [nh state] (set-gripper-separation nh true (:separation state))) 







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arms ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(derive ::LeftArmState ::ArmState)
(derive ::LeftArmState ::Left)
(derive ::RightArmState ::ArmState)
(derive ::RightArmState ::Right)

(defstruct robot-arm-state     :type :tucked? :joint-angle-map) ;:gripper-state

(defn make-robot-arm-state [right? tucked? joint-angle-map]
  (struct robot-arm-state (if right? ::RightArmState ::LeftArmState) tucked? joint-angle-map))

(defmethod get-joint-map ::ArmState [obj] (:joint-angle-map obj))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Get, move to state ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn get-current-arm-state-msg [nh right?]
  (call-srv nh (str "/" (if right? "r" "l") 
		    "_arm_joint_trajectory_controller/TrajectoryQuery" )
	    (map-msg {:class TrajectoryQuery$Request :trajectoryid -1})))

(defn get-current-arm-state [nh right?]
  (let [{:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)]
    (make-robot-arm-state right? false (apply hash-map (interleave jointnames jointpositions)))))



(defn move-arm-directly-to-state [#^NodeHandle nh arm-state]
  (let [right? (isa? (:type arm-state) ::Right)
	{:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)]
    (call-srv (str "/" (if right? "r" "l") "_arm_joint_trajectory_controller/TrajectoryStart")
      (map-msg
       {:class TrajectoryStart$Request :hastiming 0 :requesttiming 0
	:traj {:class JointTraj
	       :points (for [state [jointpositions (map (:joint-angle-map arm-state) jointnames)]]
			 {:class JointTrajPoint :positions state :time 0})}}))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tuck and untuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *larm-up-state*
  (make-robot-arm-state false false 
    (into {} [["l_shoulder_pan_joint" 1.0334563255310059] ["l_shoulder_lift_joint" -0.21823130548000336] ["l_upper_arm_roll_joint" 0.11569690704345703] ["l_elbow_flex_joint" -1.0827234983444214] ["l_forearm_roll_joint" -2.9299917221069336] ["l_wrist_flex_joint" 0.10728263854980463] ["l_wrist_roll_joint" -1.6954907178878784]])))

(def *rarm-up-state*
  (make-robot-arm-state true false   
    (into {} [["r_shoulder_pan_joint" -1.0606677532196045] ["r_shoulder_lift_joint" -0.33650094270706177] ["r_upper_arm_roll_joint" -0.0998004600405693] ["r_elbow_flex_joint" -0.9744399189949036] ["r_forearm_roll_joint" 3.1062114238739014] ["r_wrist_flex_joint" 0.1390128135681152] ["r_wrist_roll_joint" 2.7358944416046143]])))

(def *larm-tucked-state*  
  (make-robot-arm-state false true 
    (into {} [["l_shoulder_pan_joint" 4.57763671875E-5] ["l_shoulder_lift_joint" 1.050065517425537] ["l_upper_arm_roll_joint" 1.5704517364501953] ["l_elbow_flex_joint" -2.0499651432037354] ["l_forearm_roll_joint" -1.5006138710305095E-5] ["l_wrist_flex_joint" 0.10002660751342773] ["l_wrist_roll_joint" -4.604033892974218E-4]])))

(def *rarm-tucked-state*
  (make-robot-arm-state true true  
    (into {} [["r_shoulder_pan_joint" -4.7210945922415704E-5] ["r_shoulder_lift_joint" 1.3463068008422852] ["r_upper_arm_roll_joint" -1.5700957775115967] ["r_elbow_flex_joint" -1.57080078125] ["r_forearm_roll_joint" -1.3014320575166494E-4] ["r_wrist_flex_joint" 0.0999908447265625] ["r_wrist_roll_joint" 2.1505355834960382E-4]])))



(defn throw-arms [#^NodeHandle nh]
  (doseq [s [*larm-up-state* *rarm-up-state*]] (move-arm-directly-to-state nh s)))

(defn tuck-arms [#^NodeHandle nh]
  (move-arm-directly-to-state nh *rarm-tucked-state*)
  (Thread/sleep 4000)
  (move-arm-directly-to-state nh *larm-tucked-state*))

(defn throw-and-tuck-arms [#^NodeHandle nh]
  (throw-arms nh) (Thread/sleep 10000) (tuck-arms nh))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Inverse Kinematics ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: random joint configs.
; TODO: not very useful without collision checking of IK solutions.
(defn inverse-kinematics
  "Returns a final joint map (possibly in collision) or nil for failure.
   If pose-stamped is in a frame where non-arm joints are relevant, they should be provided."
  [#^NodeHandle nh right? pose-stamped init-joint-map]
  (let [init-joints (seq init-joint-map)]
    (try 
     (into {} (map vector (map first init-joints) 
       (:solution (call-srv nh (str "/pr2_ik_" (if right? "right" "left") "_arm/ik_service")  
		    (map-msg 
		     {:class IKService$Request
		      :data {:class IKRequest
			     :joint_names (map first init-joints)
			     :positions   (map second init-joints)
			     :pose_stamped pose-stamped}})))))
     (catch RosException e
       nil
       ))))

; (inverse-kinematics nh true {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.53 :y -0.02 :z -0.38} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 0.0 :w 1.0}}} (:joint-angle-map (get-current-arm-state nh true)))

;(defn rand-double [[mn mx]]
;  (+ mn (rand (- mx mn))))
;
;  (def *rarm-joint-limits*
;       (into {}
;	 (for [j (map first (get-arm-joints true))]
;	   [j
;	    (if-let [p (get *robot-joint-limits* j)]
;	        (vec (map read-string p))
;	      [(- Math/PI) Math/PI])])))
;  (def *larm-joint-limits*
;       (into {}
;	 (for [j (map first (get-arm-joints false))]
;	   [j
;	    (if-let [p (get *robot-joint-limits* j)]
;	        (vec (map read-string p))
;	      [(- Math/PI) Math/PI])])))
;(defn rand-joint-config [right?]
;  (into {}
;    (map (fn [[k v]] [k (rand-double v)]) (if right? *rarm-joint-limits* *larm-joint-limits*))))


;(defn move-arm-directly-to-pose [nh right? pose-stamped ]
;  (when-let [joints (compute-ik nh pose-stamped (get-arm-joints right?))]
;    (println joints)))
;    (move-arm-directly-to nh right? (into {} joints))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Arm Planning  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *tll-header* {:class Header :frame_id "/torso_lift_link"})
(def *bl-header* {:class Header :frame_id "/base_link"})
(def *map-header* {:class Header :frame_id "/map"})

(def *shared-arm-params*
     {:class KinematicSpaceParameters
      :distance_metric "L2Square" :planner_id      ""
      :volumeMin       {:class PointStamped :header *map-header* :point {:class Point :x 0 :y 0 :z 0}}
      :volumeMax       {:class PointStamped :header *map-header* :point {:class Point :x 0 :y 0 :z 0}}})
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
       :toleranceAbove [tol]
       :toleranceBelow [tol]})))

(defn make-kinematic-joint [[joint-name joint-position]]
  {:class KinematicJoint :header (assoc *map-header* :stamp (.subtract (.now *ros*) (Duration. 0.1)))
   :joint_name joint-name :value (if (coll? joint-position) (vec (map double joint-position)) [(double joint-position)])})
  

(defn encode-xyz-pose-constraint-type [x? y? z?]
  (cond (and x? y? z?) PoseConstraint/POSITION_XYZ
	(and x? y?   ) PoseConstraint/POSITION_XY
	(and    y? z?) PoseConstraint/POSITION_YZ
	(and x?    z?) PoseConstraint/POSITION_XZ
	x?             PoseConstraint/POSITION_X
	x?             PoseConstraint/POSITION_Y
	x?             PoseConstraint/POSITION_Z
	:else          0))

(defn encode-rpy-pose-constraint-type [r? p? y?]
  (cond (and r? p? y?) PoseConstraint/ORIENTATION_RPY
	(and r? p?   ) PoseConstraint/ORIENTATION_RP
	(and    p? y?) PoseConstraint/ORIENTATION_PY
	(and r?    y?) PoseConstraint/ORIENTATION_RY
	r?             PoseConstraint/ORIENTATION_R
	p?             PoseConstraint/ORIENTATION_P
	y?             PoseConstraint/ORIENTATION_Y
	:else          0))

(defn encode-pose-constraint-type [[x? y? z?] [roll? pitch? yaw?]]
  (+ (encode-xyz-pose-constraint-type x? y? z?)
     (encode-rpy-pose-constraint-type roll? pitch? yaw?)))

; TODO: nice, abstract position, orientation representations.

(defn encode-pose-constraint 
  ([right? frame [x y z] [ax ay az] angle]
     (encode-pose-constraint right? frame [x y z] [ax ay az] angle [true true true] [true true true]))
  ([right? frame [x y z] [ax ay az] angle [x? y? z?] [roll? pitch? yaw?]]
  {:class PoseConstraint :type (encode-pose-constraint-type [x? y? z?] [roll? pitch? yaw?])
   :position_distance 0.001 :orientation_distance 0.001 :orientation_importance 0.5
   :link_name (str (if right? "r" "l") "_gripper_palm_link")
   :pose {:class PoseStamped
	  :header {:class Header :frame_id frame}
	  :pose   {:class Pose 
		   :position    {:class Point :x x :y y :z y}
		   :orientation (axis-angle->quaternion-msg [ax ay az] angle)}}}))
  
(defn plan-arm-motion
  "joint constraints are passed as map from name to either value,  
   which will use this tolerance, or interval, or joint_constraint map.
   pose constraints are lists of PoseConstraints maps -- no shortcuts for now.
   Init-joints should include base and torso, in general."
  [#^NodeHandle nh right? world robot-state joint-constraints pose-constraints]
  (put-single-message "collision_map_future" (map-msg (world->collision-map world)) 1)
  (call-srv nh "/plan_kinematic_path"
   (map-msg 
     {:class MotionPlan$Request :times 1 :allowed_time 0.5
      :params (if right? *rarm-params* *larm-params*)
      :start_state      (doall (map make-kinematic-joint (get-joint-map robot-state)))
      :path_constraints *no-constraints*
      :goal_constraints {:class KinematicConstraints 
			 :pose_constraint (vec pose-constraints)
			 :joint_constraint (vec (map parse-joint-constraint joint-constraints))}})))


(defn describe-motion-plan [plan]
  (if (empty? (:states (:path plan)))
      (println "No plan was found")
    (println 
     (str (if (:unsafe plan) "unsafe ") 
	  (if (:approximate plan) (str "approximate, with distance " (:distance plan) " "))
	  "plan with " (count (:states (:path plan))) " states, time " (last (:times (:path plan)))
	  " found."))))


(defn move-arm-to-state 
  "Actually move arm to state using move_arm action, with replanning, synchronously"
  [#^NodeHandle nh arm-state]
  (run-action nh (str "/move_" (if (isa? (:type arm-state) ::Right) "right" "left") "_arm") 
    (map-msg {:class MoveArmGoal 
	      :path_constraints *no-constraints*
	      :goal_constraints {:class KinematicConstraints 
				 :pose_constraint  []
				 :joint_constraint (vec (map parse-joint-constraint 
							     (:joint-angle-map arm-state)))}})
    (MoveArmState.)))

; Warning! TODO! planning in base_link may cause problems...



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Torso ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct robot-torso-state   :type :height)

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

(defstruct robot-state         :type :base :torso :larm :rarm :lgripper :rgripper)
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




(set! *warn-on-reflection* false)




(comment
(do (use 'ros.ros 'ros.world 'ros.robot :reload-all) (import-ros)
(defmsgs [ros.pkg
	  [roslib.msg Header]
	  [std_msgs.msg ColorRGBA Float64]
	  [robot_msgs.msg
	     OccGrid MapMetaData 
	     Point PointStamped Vector3 Quaternion
	     Velocity AngularVelocity Acceleration AngularAcceleration 
	     Pose PoseDot PoseDDot PoseStamped PoseWithRatesStamped]
	  [robot_actions.msg ActionStatus] 
	  [nav_robot_actions.msg MoveBaseState]
	  [motion_planning_msgs.msg 
	   JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath ]
	  [manipulation_msgs.msg JointTrajPoint JointTraj IKRequest ]
;	 [topological_map.msg Cell Connector ConnectorEdge MapRegion]
	  [visualization_msgs.msg Polyline]
	  [pr2_robot_actions.msg MoveArmGoal MoveArmState]
	  [mechanism_msgs.msg JointState ActuatorState MechanismState]
	  ])



(defsrvs [ros.pkg
	  [pr2_mechanism_controllers.srv TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [motion_planning_srvs.srv MotionPlan]
	  [manipulation_srvs.srv    IKService]
	  [tf_node.srv              TransformPoint TransformPose]
	  [navfn.srv SetCostmap MakeNavPlan]
;	  [robot_srvs.srv StaticMap]
;	  [topological_map.srv GetTopologicalMap]
	  ]))

; (call-srv "/tf_node/transform_point" (map-msg {:class TransformPoint$Request :target_frame "/map" :pin {:class PointStamped :header {:class Header :frame_id "/odom" :stamp (.subtract (.now *ros*) (Duration. 0.1))} :point {:class Point :x 0 :y 0 :z 0}} :fixed_frame "" :target_time (Time.)}))

; (count (:times (:path (plan-arm-motion nh true (get-initial-world 0.1 0.1 0) (assoc (get-current-robot-state nh)  :base (make-robot-base-state 8 9 0) :torso (make-robot-torso-state 0.2)) (:joint-angle-map *rarm-tucked-state*) nil))))
)