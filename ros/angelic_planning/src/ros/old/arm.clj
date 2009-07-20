;///////////////////////////////////////////////////////////////////////////////
;// Functions for arm planning in Clojure
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



(ns ros.arm
  (:use   clojure.xml ros.ros)
	  )
  
(set! *warn-on-reflection* true)


(import-ros)

(defmsgs [ros.pkg 
	  [roslib.msg Header]
	  [std_msgs.msg Float64]
	  [robot_msgs.msg Point PointStamped Pose Velocity AngularVelocity PoseDot Acceleration AngularAcceleration PoseDDot Quaternion PoseStamped PoseWithRatesStamped ]
	  [robot_actions.msg ActionStatus] 
	  [motion_planning_msgs.msg JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath ]
	  [manipulation_msgs.msg JointTrajPoint JointTraj IKRequest ]
	  [pr2_robot_actions.msg MoveArmGoal MoveArmState]])

(defsrvs [ros.pkg
	  [pr2_mechanism_controllers.srv TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [motion_planning_srvs.srv KinematicPlan]
	  [manipulation_srvs.srv    IKService]
	  [tf_node.srv              TransformPoint TransformPose]])


;(defonce *larm-joint-names* nil)
;(defonce *rarm-joint-names* nil)

(defn get-arm-joints 
  ([right?] (with-node-handle [nh] (get-arm-joints nh right?)))
  ([nh right?]
     (let [m (call-srv nh (str "/" (if right? "r" "l") 
			       "_arm_joint_trajectory_controller/TrajectoryQuery" )
		       (map-msg {:class TrajectoryQuery$Request :trajectoryid -1}))]
       (map vector (safe-get* m :jointnames) (safe-get* m :jointpositions)))))



(defn string->input-stream [#^String s] 
 (java.io.ByteArrayInputStream. (.getBytes s "UTF-8")))

(defonce *robot-xml* nil)
(defonce *robot-joint-limits* nil)
(defonce *rarm-joint-limits* nil)
(defonce *larm-joint-limits* nil)

(defn get-robot-xml []
  (def *robot-xml* 
       (parse (with-node-handle [nh] (string->input-stream (.getStringParam nh "/robotdesc/pr2")))))
  (def *robot-joint-limits*
       (into {}
	 (for [joint (:content *robot-xml*)
	       :when (and (= (:tag joint) :joint)
			  (every? (or (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) {})
				  [:min :max]))]
	   [(:name (:attrs joint))
	    (vec (map (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) [:min :max]))])))
  (def *rarm-joint-limits*
       (into {}
	 (for [j (map first (get-arm-joints true))]
	   [j
	    (if-let [p (get *robot-joint-limits* j)]
	        (vec (map read-string p))
	      [(- Math/PI) Math/PI])])))
  (def *larm-joint-limits*
       (into {}
	 (for [j (map first (get-arm-joints false))]
	   [j
	    (if-let [p (get *robot-joint-limits* j)]
	        (vec (map read-string p))
	      [(- Math/PI) Math/PI])])))
  )



(def *rarm-params*
     {:class KinematicSpaceParameters
      :model_id        "right_arm"
      :distance_metric "L2Square"
      :planner_id      ""
      :volumeMin       {:class Point :x 0 :y 0 :z 0}
      :volumeMax       {:class Point :x 0 :y 0 :z 0}})

(def *larm-params*
     {:class KinematicSpaceParameters
      :model_id        "left_arm"
      :distance_metric "L2Square"
      :planner_id      ""
      :volumeMin       {:class Point :x 0 :y 0 :z 0}
      :volumeMax       {:class Point :x 0 :y 0 :z 0}})

(def *no-constraints* {:class KinematicConstraints :joint_constraint [] :pose_constraint []})


(defn l2-distance [v1 v2]
   (Math/sqrt (reduce + (map #(let [x (- (double %1) (double %2))] (* x x)) v1 v2))))

(def *tll-header* {:class Header :frame_id "torso_lift_link"})


(defn make-kinematic-joint [[joint-name joint-position]]
  {:class KinematicJoint
   :header *tll-header*
   :joint_name joint-name :value [(double joint-position)]})

  
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


(defn get-motion-plan 
  "joint constraints are passed as map from name to either value,  
   which will use this tolerance, or interval, or joint_constraint map.

   pose constraints are lists of PoseConstraints maps -- no shortcuts for now."
  ([nh right? joint-constraints pose-constraints] 
     (get-motion-plan nh right? {} joint-constraints pose-constraints))
  ([#^NodeHandle nh right? init-joint-pairs joint-constraints pose-constraints]
  (let [srv (.serviceClient nh "/plan_kinematic_path" (KinematicPlan.) true)]
    (msg-map 
     (.call srv 
       (map-msg 
;     (println 
	 {:class KinematicPlan$Request
	  :times 1
	  :allowed_time 0.5
	  :params (if right? *rarm-params* *larm-params*)
	  :start_state      (map make-kinematic-joint init-joint-pairs)
	  :path_constraints *no-constraints*
	  :goal_constraints {:class KinematicConstraints 
			     :pose_constraint (vec pose-constraints)
			     :joint_constraint (vec (map parse-joint-constraint joint-constraints))}}
	 ))))))



(defn check-plan [plan]
  (assert (seq (:states (:path plan))))
  (assert (zero? (:unsafe plan)))
  ; not checking frame or model of plan
  (when-not (zero? (:approximate plan))
    (println "Got approximate plan.  Distance to goal is" (:distance plan)))
  (println "Plan has " (count (:states (:path plan))) " states, l2 distance " 
	   (reduce + (map #(apply l2-distance %) 
			  (partition 2 1 (map :vals (:states (:path plan)))))))
  plan)

(defn plan->trajectory [plan]
  {:class JointTraj
   :points 
     (for [state (:states (:path plan))]
       {:class JointTrajPoint 
	:positions (:vals state)
	:time 0})})

(defn execute-plan [plan right?]
  (call-srv (str "/" (if right? "r" "l") "_arm_joint_trajectory_controller/TrajectoryStart")
	    (map-msg
	     {:class TrajectoryStart$Request
	      :hastiming 0 :requesttiming 0
	      :traj (plan->trajectory plan)})))


(defn rand-double [[mn mx]]
  (+ mn (rand (- mx mn))))

(defn rand-joint-config [right?]
  (into {}
    (map (fn [[k v]] [k (rand-double v)]) (if right? *rarm-joint-limits* *larm-joint-limits*))))

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

; For now, do simple IK, not the rancy random-retry, checked thing in move_arm.
(defn compute-ik 
;  ([#^NodeHandle nh pose-stamped]
;     (compute-ik nh pose-stamped (get-rarm-joints)))
  ([#^NodeHandle nh pose-stamped init-joints]
     (compute-ik nh pose-stamped init-joints 0))
  ([#^NodeHandle nh pose-stamped init-joints random-tries]  
     (try 
      (map vector (map first init-joints) (:solution 
       (call-srv nh "/pr2_ik_node/ik_service"  
        (map-msg 
	 {:class IKService$Request
	  :data {:class IKRequest
		 :joint_names (map first init-joints)
		 :positions   (map second init-joints)
		 :pose_stamped pose-stamped}}))))
      (catch RosException e
	(println "IK failed ...")
	(when (> random-tries 0)
	  (compute-ik nh pose-stamped (rand-joint-config) (dec random-tries)))))))

(defn get-motion-plan-ik [nh right? pose-stamped ]
  (when-let [joints (compute-ik nh pose-stamped (get-arm-joints right?))]
    (get-motion-plan nh right? joints [])))


(def *larm-up-joints*
  (into {} [["l_shoulder_pan_joint" 1.0334563255310059] ["l_shoulder_lift_joint" -0.21823130548000336] ["l_upper_arm_roll_joint" 0.11569690704345703] ["l_elbow_flex_joint" -1.0827234983444214] ["l_forearm_roll_joint" -2.9299917221069336] ["l_wrist_flex_joint" 0.10728263854980463] ["l_wrist_roll_joint" -1.6954907178878784]]))

(def *rarm-up-joints*  
  (into {} [["r_shoulder_pan_joint" -1.0606677532196045] ["r_shoulder_lift_joint" -0.33650094270706177] ["r_upper_arm_roll_joint" -0.0998004600405693] ["r_elbow_flex_joint" -0.9744399189949036] ["r_forearm_roll_joint" 3.1062114238739014] ["r_wrist_flex_joint" 0.1390128135681152] ["r_wrist_roll_joint" 2.7358944416046143]]))


(def *larm-tucked-joints*  
  (into {} [["l_shoulder_pan_joint" 4.57763671875E-5] ["l_shoulder_lift_joint" 1.050065517425537] ["l_upper_arm_roll_joint" 1.5704517364501953] ["l_elbow_flex_joint" -2.0499651432037354] ["l_forearm_roll_joint" -1.5006138710305095E-5] ["l_wrist_flex_joint" 0.10002660751342773] ["l_wrist_roll_joint" -4.604033892974218E-4]]))

(def *rarm-tucked-joints*
  (into {} [["r_shoulder_pan_joint" -4.7210945922415704E-5] ["r_shoulder_lift_joint" 1.3463068008422852] ["r_upper_arm_roll_joint" -1.5700957775115967] ["r_elbow_flex_joint" -1.57080078125] ["r_forearm_roll_joint" -1.3014320575166494E-4] ["r_wrist_flex_joint" 0.0999908447265625] ["r_wrist_roll_joint" 2.1505355834960382E-4]]))

(defn move-arm-directly-to [#^NodeHandle nh right? joint-map]
  (let [cpos (get-arm-joints nh right?)
	joint-names (map first cpos)]
    (call-srv (str "/" (if right? "r" "l") "_arm_joint_trajectory_controller/TrajectoryStart")
	      (map-msg
	       {:class TrajectoryStart$Request
		:hastiming 0 :requesttiming 0
		:traj {:class JointTraj
		       :points 
		       (for [state [(map second cpos) (map joint-map joint-names)]]
			 {:class JointTrajPoint 
			  :positions state
			  :time 0})}}))))

(defn move-arm-directly-to-pose [nh right? pose-stamped ]
  (when-let [joints (compute-ik nh pose-stamped (get-arm-joints right?))]
;    (println joints)))
    (move-arm-directly-to nh right? (into {} joints))))


(defn set-torso-position [#^NodeHandle nh pos]
  (put-single-message nh "/torso_lift_controller/set_command" 
		      (map-msg {:class Float64 :data pos}) 1))

(defn throw-arms [#^NodeHandle nh]
  (move-arm-directly-to nh false *larm-up-joints*)
  (move-arm-directly-to nh true *rarm-up-joints*))

;  (execute-plan (check-plan
;    (get-motion-plan nh false *larm-up-joints* nil)) false)
;  (Thread/sleep 15000)
;  (execute-plan (check-plan
;    (get-motion-plan nh true *rarm-up-joints* nil)) true))


(defn tuck-arms [#^NodeHandle nh]
  (move-arm-directly-to nh true *rarm-tucked-joints*)
  (Thread/sleep 4000)
  (move-arm-directly-to nh false *larm-tucked-joints*))


(defn throw-and-tuck-arms [#^NodeHandle nh]
  (throw-arms nh) (Thread/sleep 10000) (tuck-arms nh))


(def *cylinder-center* {:class Point :x 2.621 :y -0.0092 :z 0.6973})
;(def *cylinder-radius* 

(defn set-gripper-separation [#^NodeHandle nh right? sep]
  (put-single-message (str (if right? "r" "l") "_gripper_position_controller/set_command")
		      (map-msg {:class Float64 :data (double sep)})))


(defn get-current-pose [#^NodeHandle nh]
  (get-single-message nh "/base_pose_ground_truth" (PoseWithRatesStamped.)))

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

(defn move-to-pose 
  ([nh pose]
     (move-to-pose nh pose nil))
  ([#^NodeHandle nh pose wait-for-dist?]
  (put-single-message nh "/move_base/activate"  		      
    (map-msg {:class PoseStamped :header {:class Header :frame_id "/map"} 
	      :pose pose}) 1)
  (when wait-for-dist? (println "wait...")
    (while (> (pose-distance pose (:pos (get-current-pose nh)) 1.0) wait-for-dist?)
      (Thread/sleep 100)))))
    

(defn move-to-waypoint [nh]
  (move-to-pose nh 
		{:orientation {:x -7.096677899210499E-5, :y -1.6137608737673157E-6, :z -0.0000105626865617, :w 1.0, :class ros.pkg.robot_msgs.msg.Quaternion}, 
		 :position {:x 28.297188345336477, :y 27.756744656335115, :z 0.0364089825477093, :class ros.pkg.robot_msgs.msg.Point}, :class ros.pkg.robot_msgs.msg.Pose}
		1.0))

(defn move-to-spot [nh]
  (move-to-pose nh
   {:orientation {:x 0.0, :y 0.0, :z -1.0, :w 0.0, :class ros.pkg.robot_msgs.msg.Quaternion}, :position {:x 29.597188345336477, :y 25.656744656335115, :z 0.0364089825477093, :class ros.pkg.robot_msgs.msg.Point}, :class ros.pkg.robot_msgs.msg.Pose}
   0.3))

(defn move-forward [#^NodeHandle nh steps]
  (let [pub (.advertise nh "/cmd_vel" (PoseDot.) 30)] 
    (dotimes [_ (Math/abs (int steps))] 
      (Thread/sleep 100) 
      (.publish pub (map-msg {:class PoseDot :vel {:class Velocity :vx (* 0.5 (Math/signum (double steps)) 2) :vy 0 :vz 0} 
			      :ang_vel {:class AngularVelocity :vx 0 :vy 0 :vz 0}})))
    (.shutdown pub)))

(defn get-in-position [#^NodeHandle nh]
  (println "Tucking arms")
  (tuck-arms nh)
  (Thread/sleep 10000)
  (println "Moving to waypoint")
  (move-to-waypoint nh)
  (println "Moving to spot")
  (move-to-spot nh)
  (println "Throwing arms, lifting torso, moving forward, opening gripper")
  (throw-arms nh)
  (set-torso-position nh 0.3)
  (move-forward nh 20)
  (set-gripper-separation nh true 0.1)
  )
 

; (def nh (.createNodeHandle *ros*))

; (with-node-handle [nh] (let [pub (.advertise nh "/cmd_vel" (PoseDot.) 30)] (dotimes [_ 20] (Thread/sleep 100) (.publish pub (map-msg {:class PoseDot :vel {:class Velocity :vx 1.0 :vy 0 :vz 0} :ang_vel {:class AngularVelocity :vx 0 :vy 0 :vz 0}})))))

; plans have consistent l2 distance between points:
; (map #(apply l2-distance %) (partition 2 1 (map :vals (:states (:path *plan*)))))

; in torso_lift_link frame,arm straight out has hand
; (r_gripper_palm_link) at about {:class Point :x 0.85 :y -0.2 :z 0.9}
; (x is out, y is left, z is up.)
 
; (with-node-handle [nh] (execute-plan (check-plan (get-motion-plan nh true nil [{:class PoseConstraint :type PoseConstraint/POSITION_XYZ :link_name "r_gripper_palm_link" :pose {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.85 :y -0.2 :z 0.9} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 0.0 :w 1.0}}} :position_distance 0.00001 :orientation_distance 0.0 :orientation_importance 0.0}])) true))

; (with-node-handle [nh] (execute-plan (check-plan (get-motion-plan-ik nh true {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.45 :y -0.2 :z 0.00} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 1.0 :w 0.0}}})) true))


; (with-node-handle [nh] (execute-plan (check-plan (get-motion-plan nh (into {} (compute-ik nh {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.5 :y -0.2 :z 0.5} :orientation (axis-angle->quaternion-msg [0 0 1] 0)}} (get-rarm-joints) 5)) nil))))

;(with-node-handle [nh] (compute-ik nh {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.45 :y -0.2 :z 0.00} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 1.0 :w 0.0}}} (get-arm-joints true)))

(set! *warn-on-reflection* false)

;; Successful grasp!
; (with-node-handle [nh] (execute-plan (check-plan (get-motion-plan-ik nh true {:class PoseStamped :header *tll-header* :pose {:class Pose :position {:class Point :x 0.53 :y -0.02 :z -0.38} :orientation {:class Quaternion :x 0.0 :y 0.0 :z 0.0 :w 1.0}}})) true))


; (with-node-handle [nh] )


(comment 
  (defn move-arm-test []
  (put-single-message "/move_arm/activate"
  (map-msg
   {:class MoveArmGoal
    :path_constraints {:class KinematicConstraints :joint_constraint [] :pose_constraint []}
    :goal_constraints 
      {:class KinematicConstraints 
       :pose_constraint []
       :joint_constraint 
        [{:class JointConstraint
	  :header *tll-header*
	  :joint_name "r_wrist_flex_joint"
	  :value          [-0.10]
	  :toleranceAbove [0.01]
	  :toleranceBelow [0.01]}]}})
  )))