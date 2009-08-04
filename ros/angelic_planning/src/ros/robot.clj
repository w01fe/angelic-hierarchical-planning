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
	  )
  
(set! *warn-on-reflection* true)

(import-ros)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Msgs, Helpers, Etc ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmsgs  [std_msgs Float64]
	  [geometry_msgs PointStamped PoseStamped PoseWithRatesStamped]
	  [nav_robot_actions MoveBaseState]
	  [motion_planning_msgs 
	   JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath]
	  [manipulation_msgs JointTraj IKRequest]
	  [pr2_robot_actions MoveArmGoal MoveArmState ActuateGripperState]
	  [mechanism_msgs    MechanismState]
	  )

(defsrvs  [pr2_mechanism_controllers TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [motion_planning_srvs MotionPlan]
	  [manipulation_srvs    IKService]
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


(defstruct robot-base-state    :class :x :y :theta)

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
   :header {:frame_id "/map"}
   :pose   {:position {:x (:x base-state) :y (:y base-state) :z 0}
	    :orientation (angle->quaternion (:theta base-state))}})


(defn get-current-base-pose [#^NodeHandle nh]
  (get-single-message nh "/base_pose_ground_truth" (PoseWithRatesStamped.)))

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

(defstruct robot-gripper-state :class :separation :holding)

(defn make-robot-gripper-state [right? sep holding]
  (struct robot-gripper-state (if right? ::RightGripperState ::LeftGripperState) sep holding))

(def *gripper-mul* 5.55) ; Multiplier for weird gripper joints

(defmethod get-joint-map ::GripperState [obj]
  (let [sep (:separation obj)
	cr (if (isa? (:class obj) ::Right) "r" "l")]
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
  (put-single-message nh (str (if right? "r" "l") "_gripper_position_controller/set_command")
		      (map-msg Float64 {:data (double sep)}) 1))

(defmulti move-gripper-to-state (fn [nh gs] (:class gs)))
(defmethod move-gripper-to-state ::Left [nh state] (set-gripper-separation nh false (:separation state))) 
(defmethod move-gripper-to-state ::Right [nh state] (set-gripper-separation nh true (:separation state))) 







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

(defn get-current-arm-state-msg [nh right?]
  (call-srv-cached nh (str "/" (if right? "r" "l") 
		    "_arm_joint_trajectory_controller/TrajectoryQuery" )
	    (map-msg TrajectoryQuery$Request {:trajectoryid -1})))

(defn get-current-arm-state [nh right?]
  (let [{:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)]
    (make-robot-arm-state right? false (apply hash-map (interleave jointnames jointpositions)))))



(defn start-trajectory [#^NodeHandle nh srv-prefix joint-traj]
  (safe-get*
   (call-srv-cached nh (str srv-prefix "/TrajectoryStart")
      (map-msg TrajectoryStart$Request
       {:hastiming 0 :requesttiming 0
	:traj joint-traj}))
   :trajectoryid))

(defonce *good-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Done])))

(defonce *bad-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Deleted
		 TrajectoryQuery$Response/State_Failed
		 TrajectoryQuery$Response/State_Canceled
		 ])))

(defn wait-for-trajectory [#^NodeHandle nh srv-prefix traj-id]
  (print "Waiting for trajectory" traj-id "...")
  (loop []
   (let [outcome (int (:done (call-srv (str srv-prefix "/TrajectoryQuery")
				      (map-msg TrajectoryQuery$Request
					       {:trajectoryid traj-id}))))]
    (cond (*good-traj-outcomes* outcome) (do (println outcome) true)
	  (*bad-traj-outcomes* outcome) (do (println outcome) false)
	  :else (do (print outcome)
		    (Thread/sleep 100)
		    (recur))))))



(defn move-arm-directly-to-state 
  ([#^NodeHandle nh arm-state]
     (move-arm-directly-to-state nh arm-state true))
  ([#^NodeHandle nh arm-state wait?]
    (let [right? (isa? (:class arm-state) ::Right)
	  {:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)
	  srv-prefix (str "/" (if right? "r" "l") "_arm_joint_trajectory_controller")
	  id (start-trajectory nh srv-prefix
	       {:names jointnames
		:points (for [state [jointpositions (map (:joint-angle-map arm-state) jointnames)]]
			  {:positions state :time 0})})]
      (or (and (not wait?) [srv-prefix id])
	  (wait-for-trajectory nh srv-prefix id)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tuck and untuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *larm-up-state*
  (make-robot-arm-state false false 
    (into {} [["l_shoulder_pan_joint" 1.0334563255310059] ["l_shoulder_lift_joint" -0.21823130548000336] ["l_upper_arm_roll_joint" 0.11569690704345703] ["l_elbow_flex_joint" -1.0827234983444214] ["l_forearm_roll_joint" -2.9299917221069336] ["l_wrist_flex_joint" 0.10728263854980463] ["l_wrist_roll_joint" -1.6954907178878784]])))

(def *rarm-up-state*
  (make-robot-arm-state true false   
    (into {} [["r_shoulder_pan_joint" -1.0606677532196045] ["r_shoulder_lift_joint" -0.33650094270706177] ["r_upper_arm_roll_joint" -0.0998004600405693] ["r_elbow_flex_joint" -0.9744399189949036] ["r_forearm_roll_joint" 3.1062114238739014] ["r_wrist_flex_joint" 0.1390128135681152] ["r_wrist_roll_joint" 2.7358944416046143]])))

(def *larm-tucked-state*  
  (make-robot-arm-state false true 
    {"l_shoulder_lift_joint" 0.900306510925293, "l_wrist_flex_joint" 0.10485601425170898, "l_wrist_roll_joint" -0.07251530140638351, "l_elbow_flex_joint" -1.281473660469055, "l_forearm_roll_joint" -0.13328810036182404, "l_upper_arm_roll_joint" 1.399874210357666, "l_shoulder_pan_joint" 0.0091785430908203}
    ;(into {} [["l_shoulder_pan_joint" 4.57763671875E-5] ["l_shoulder_lift_joint" 1.050065517425537] ["l_upper_arm_roll_joint" 1.5704517364501953] ["l_elbow_flex_joint" -2.0499651432037354] ["l_forearm_roll_joint" -1.5006138710305095E-5] ["l_wrist_flex_joint" 0.10002660751342773] ["l_wrist_roll_joint" -4.604033892974218E-4]])
    ))

(def *rarm-tucked-state*
  (make-robot-arm-state true true  
    {"r_wrist_flex_joint" 0.10194683074951172, "r_wrist_roll_joint" 2.2315979003905862E-4, "r_shoulder_lift_joint" 1.2862510108947754, "r_elbow_flex_joint" -1.5709961652755737, "r_forearm_roll_joint" -9.14452102733776E-5, "r_upper_arm_roll_joint" -1.5699418783187866, "r_shoulder_pan_joint" -1.8587072554510087E-4}
    ;(into {} [["r_shoulder_pan_joint" -4.7210945922415704E-5] ["r_shoulder_lift_joint" 1.3463068008422852] ["r_upper_arm_roll_joint" -1.5700957775115967] ["r_elbow_flex_joint" -1.57080078125] ["r_forearm_roll_joint" -1.3014320575166494E-4] ["r_wrist_flex_joint" 0.0999908447265625] ["r_wrist_roll_joint" 2.1505355834960382E-4]])
    ))



(defn throw-arms [#^NodeHandle nh]
  (doseq [[p id] (doall (for [s [*larm-up-state* *rarm-up-state*]]
		    (move-arm-directly-to-state nh s false)))]
    (wait-for-trajectory nh p id))) 


(defn tuck-arms [#^NodeHandle nh]
  (doseq [[p id] [(move-arm-directly-to-state nh *rarm-tucked-state* false)
		(do (Thread/sleep 6000)
		    (move-arm-directly-to-state nh *larm-tucked-state* false))]]
    (wait-for-trajectory nh p id)))
  

(defn throw-and-tuck-arms [#^NodeHandle nh]
  (throw-arms nh) (tuck-arms nh))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Kinematics ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: random joint configs.
; TODO: not very useful without collision checking of IK solutions.
; Pose is for something like, but not exactly, palm link.
(defn inverse-kinematics
  "Returns a final joint map (possibly in collision) or nil for failure.
   Pose-stamped must be in the torso_lift_link frame."
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


(defn forward-kinematics
  "Returns a lazy seq [in-collision? poses], where poses is a map
   from link names to poses.  Assumes joints in map frame.
   If in_collision is to be accurate, must first publish a collision map
   to the appropriate topic in the fk_node.  For now, response is in some
   unknown frame."
 [#^NodeHandle nh joint-map]
   (let [res (call-srv-cached nh "/fk_node/forward_kinematics"
	      (map-msg {:class ForwardKinematics$Request
			:joints (map make-kinematic-joint joint-map)}))]
;     (println res)
     (assert (= (count (:link_names res)) (count (:link_poses res))))
    (cons (> (:in_collision res) 0)
	  (lazy-seq [(apply hash-map (interleave (:link_names res) (:link_poses res)))]))))




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
    (cond (< y 0) 
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
     (let [all-joints (get-joint-map robot)]
      (loop [tries random-retries 
	    init-joints (if start-random? (random-arm-joint-map nh right?)
			    (:joint-angle-map ((if right? :rarm :larm) robot)))]
;       (println init-joints)
       (or (if-let [sol (inverse-kinematics nh right? pose-stamped init-joints)]
	     (let [collision (first (forward-kinematics nh (merge all-joints sol)))]
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
      :distance_metric "L2Square" :planner_id      ""
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
  
(defn plan-arm-motion
  "joint constraints are passed as map from name to either value,  
   which will use this tolerance, or interval, or joint_constraint map.
   pose constraints are lists of PoseConstraints maps -- no shortcuts for now.
   Init-joints should include base and torso, in general."
  [#^NodeHandle nh right? world robot-state joint-constraints pose-constraints]
  (put-single-message-cached nh "collision_map_future" (map-msg (world->collision-map world)))
;  (println "\n\n\n\n\n\n\n\n" right?)
;  (println (doall (map make-kinematic-joint (get-joint-map robot-state))))
;  (println "\n\n\n")
;  (println pose-constraints)
  (call-srv-cached nh "/plan_kinematic_path"
   (map-msg 
     {:class MotionPlan$Request :times 1 :allowed_time 0.5
      :params (if right? *rarm-params* *larm-params*)
      :start_state      (doall (map make-kinematic-joint (get-joint-map robot-state)))
      :path_constraints *no-constraints*
      :goal_constraints {:pose_constraint (vec pose-constraints)
			 :joint_constraint (vec (map parse-joint-constraint joint-constraints))}})))


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
