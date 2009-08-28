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



(in-ns 'ros.robot)
  
(defmsgs  [std_msgs Empty]
	  [geometry_msgs PoseStamped]
	  [motion_planning_msgs 
	   JointConstraint PoseConstraint KinematicConstraints
	   KinematicSpaceParameters KinematicJoint KinematicState KinematicPath]
	  [manipulation_msgs JointTraj IKRequest]
	  [move_arm MoveArmAction]
	  )

(defsrvs  [motion_planning_msgs GetMotionPlan]
          [pr2_mechanism_controllers TrajectoryStart TrajectoryQuery TrajectoryCancel]
	  [manipulation_srvs    IKService ]
	  [fk_node              ForwardKinematics]
	  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm States, getters ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(derive ::LeftArmState ::ArmState)
(derive ::LeftArmState ::Left)
(derive ::RightArmState ::ArmState)
(derive ::RightArmState ::Right)
;(derive ::MissingArmState ::ArmState)

(defstruct robot-arm-state :class :joint-angle-map :tucked?)

(defn make-robot-arm-state 
  ([right? joint-angle-map] (make-robot-arm-state right? joint-angle-map false))
  ([right? joint-angle-map tucked?]
     (struct robot-arm-state (if right? ::RightArmState ::LeftArmState) joint-angle-map tucked?)))

(defmethod get-joint-map ::ArmState [obj] (:joint-angle-map obj))
;(defmethod get-joint-map ::MissingArmState [obj] {})



(defn get-current-arm-state-msg [nh right?]
  (try 
    (call-srv-cached nh (str "/" (if right? "r" "l") 
		    "_arm_joint_waypoint_controller/TrajectoryQuery" )
	    (map-msg TrajectoryQuery$Request {:trajectoryid (TrajectoryQuery$Request/Query_Joint_Names)}))
    (catch Exception e
      (println "Presming arm missing")
      {})
  ))

(defn get-current-arm-state [nh right?]
  (let [{:keys [jointnames jointpositions]} (get-current-arm-state-msg nh right?)]
    (if jointnames 
        (make-robot-arm-state right? (apply array-map (interleave jointnames jointpositions)))
      *missing-part*)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; Joints, known configurations, utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def *arm-joints*
  ["shoulder_pan_joint" "shoulder_lift_joint" "upper_arm_roll_joint" 
   "elbow_flex_joint" "forearm_roll_joint" "wrist_flex_joint" "wrist_roll_joint"])
(def *arm-joint-wraps* [false false false false true false true])

(def *larm-joints* (map #(str "l_" %) *arm-joints*))
(def *rarm-joints* (map #(str "r_" %) *arm-joints*))

(defn get-arm-joint-names [right?]
  (if right? *rarm-joints* *larm-joints*))


;; Pumped left arm up by 0.2

(def *larm-joint-states*
     {"up"                [1.033456 -0.218231 0.115697 -1.082723 -2.929992 0.107283 -1.695491]
      "tucked"                  [0.00540709632380175 0.6378067830448103 1.591487363568815 -1.5594742423694119 -3.1409474321523534 0.10698554238260994 3.1415593943539344]
      ;[0.14540709632380175 1.0378067830448103 1.591487363568815 -1.7594742423694119 -3.1429474321523534 0.23698554238260994 3.1415593943539344]
      ;[0.144164 0.410993 1.616344 -1.771779 -8.279421 0.236909 5.131354]
      ; [-0.000020 0.899529 1.569952 -1.550905 0.000192 0.100453 -0.000417]
      "curl" [-0.108290201009834332 1.3063319912769966 0.30020155662118897 -1.99264839394572 1.5197005814266822 1.790703191104711 2.1387243534759017]
      })

(def *rarm-joint-states*
     {"up"                [-1.060668 -0.336501 -0.099800 -0.974440 3.106211 0.139013 2.735894]
      "tucked"            [ -0.297281 1.2063 -1.82473 -1.84801 0.220099 0.1 3.04481]
      ;[ -0.297281 1.3063 -1.92473 -1.64801 0.220099 0.1 3.04481]
      ;[-0.04302513181083491 1.043559686056716 -1.3698599492114338 -1.5361087707774366 0.03598088240445091 0.09429071967304825 -6.290976956420347]
      ;[0.12808 1.04762 -1.3743 -1.5358 6.3188 0.0942 -0.0078]
      ;[-0.000186 1.286251 -1.569942 -1.570996 -0.000091 0.101947 0.000223]
;      "curl"  [0.5632463281371022 1.3096314503573545 0.2748661990181705 -1.9292432892423594 11.152685215512866 1.9999383928526328 -5.118613008759258]
      "curl" [0.108290201009834332 1.3063319912769966 0.30020155662118897 -1.99264839394572 1.5197005814266822 1.790703191104711 2.4387243534759017] 
      "home"              [0.39146 0.770561 -0.593027 -1.99714 0.742525 1.60109 2.63896]
      "grasp_bar"         [-0.112613 -0.215548 -2.5479 0.002441 -0.14698 0.263452 2.53254]
      "grasp_bar_low"     [-0.0888183 -0.150892 -0.134794 -0.0605298 2.96289 0.268543 -3.0757]
      "grasp_big_table"   [-0.00313992 -0.0117858 -0.105762 -0.0776116 3.08055 0.10099 -3.01161]
      "grasp_small_table" [-0.250178 0.0616681 -0.109955 -0.118579 3.04295 0.184788 -3.0405]
      "grasp_counter"     [-0.356016 -0.188573 -0.0260828 -0.719335 -3.05293 0.870881 -2.97632]
      "drop"              [0.00685727 0.412504 -0.0828579 -1.51335 -3.08632 1.05988 -2.91744]
      })

(def *rarm-tucked-pose* [[0.17023826444898707 0.056367121113207234 0.4711496132012268] [0.6603447283989968 0.6619766211031068 0.32716708182637394 0.1367241506017992]])

(defn arm-joint-state 
  "Get an known arm joint state by name."
  ([right? name] (arm-joint-state right? name false))
  ([right? name tucked?]
     (make-robot-arm-state right?
      (if (map? name) name
	(into {} (map vector 
		      (if right? *rarm-joints* *larm-joints*)
		      (if (string? name)
			  (safe-get* (if right? *rarm-joint-states* *larm-joint-states*) name)
			name))))
      tucked?)))

(defn arm-l1-distance [j1 j2]
  (apply + (map #(Math/abs (double % )) 
    (for [[v1 v2 roll?] (map vector j1 j2 *arm-joint-wraps*)]
      (let [diff (if roll? 
		     (Math/abs (double (- (norm-angle v1) (norm-angle v2))))
		   (Math/abs (double (- v1 v2))))]
	(if roll? (if (> diff Math/PI) (- (* 2 Math/PI) diff) diff) diff))))))

(defn arm-l2-distance [j1 j2]
  (Math/sqrt (double (apply + (map #(* % %) 
    (for [[v1 v2 roll?] (map vector j1 j2 *arm-joint-wraps*)]
      (let [diff (if roll? 
		     (Math/abs (double (- (norm-angle v1) (norm-angle v2))))
		   (Math/abs (double (- v1 v2))))]
	(if roll? (if (> diff Math/PI) (- (* 2 Math/PI) diff) diff) diff))))))))


(defn interpolate-arm-joint [v1 v2 w wrap?]
  (let [v1 (norm-angle v1)
	v2 (norm-angle v2)	
	dist (double (- v2 v1))]
    (if (or (not wrap?) (< (Math/abs dist) Math/PI))
        (+ v1 (* dist w))
      (norm-angle (- v1 (* (- (* 2 Math/PI) (Math/abs dist)) (Math/signum dist) w))))))

(defn interpolate-arm-joints [j1 j2 w]
  (map (fn [v1 v2 wrap?] (interpolate-arm-joint v1 v2 w wrap?)) j1 j2 *arm-joint-wraps*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;; Forward and inverse arm kinematics ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn inverse-kinematics
  "Returns a final joint map (possibly in collision) or nil for failure.
   Pose-stamped must be a pose of a *_gripper_palm_link."
  [#^NodeHandle nh right? pose-stamped init-joint-map]
  (let [frame-in (:frame_id (:header pose-stamped))
	pose-stamped 
	 (if (= frame-in "/torso_lift_link")
	     pose-stamped
	   (do (println "Warning: IK is using TF to transform pose from"
			frame-in "to torso_lift_link.")
	       (assoc pose-stamped 
		 :header {:frame_id "/torso_lift_link"}
		 :pose   (transform-raw-pose-tf nh frame-in "/torso_lift_link" (:pose pose-stamped)))))] 
    (let [init-joints (seq init-joint-map)]
      (try 
       (let [sol 
      (into {} (map vector (map first init-joints) 
       (:solution (call-srv-cached nh (str "/pr2_ik_" (if right? "right" "left") "_arm/ik_service")  
		    (map-msg 
		     {:class IKService$Request
		      :data {:joint_names (map first init-joints)
			     :positions   (map second init-joints)
			     :pose_stamped pose-stamped}})))))]
	 ;(println sol)
	 sol)
;	 (if right? sol
;	     (assoc sol "l_wrist_roll_joint"
;		    (norm-angle (+ (sol "l_wrist_roll_joint") 2.1)))))
     (catch RosException e
       nil
       )))))

(defn out-of-safety-limits? [nh joint-map]
  (let [limits (get-robot-safe-joint-limits nh)
        [bad-j bad-v]
	(first 
	 (filter (fn [[j v]] 
		   (let [[mi mx] (get limits j [-1000 1000])]
		     (not (<= mi v mx))))
		 joint-map))]
    (when bad-j [bad-j bad-v (get limits bad-j)])))

(defn all-safety-limit-violations [nh joint-map]
  (let [limits (get-robot-safe-joint-limits nh)
	bad-jv-pairs
	 (filter (fn [[j v]] 
		   (let [[mi mx] (get limits j [-1000 1000])]
		     (not (<= mi v mx))))
		 joint-map)]
    (for [[bad-j bad-v] bad-jv-pairs]
      [bad-j bad-v (get limits bad-j)])))


(defn random-arm-joint-map [nh right?]
  (let [joint-limits (get-robot-safe-joint-limits nh)]
   (into {}
    (for [joint (get-arm-joint-names right?)
	  :let [limits (joint-limits joint)]]
      [joint (rand-double (or limits [0 (* 2 Math/PI)]))]))))

(defn limited-inverse-kinematics 
  "Try to find an IK solution that respects joint limits"
  ([#^NodeHandle nh right? pose-stamped init-joint-map random-retries]
;     (println pose-stamped)
     (loop [tries random-retries 
	    init-joints init-joint-map]
       (or (if-let [sol (time (inverse-kinematics nh right? pose-stamped init-joints))]
	       (if-let [violation (out-of-safety-limits? nh sol)]
		   (println "IK not in safety limits:" violation)
	         sol)
	     (println "IK solution not found."))
	   (when (> tries 0)
	     (recur (dec tries) (random-arm-joint-map nh right?)))))))



(defn- make-kinematic-joint [[joint-name joint-position]]
  {:class KinematicJoint 
   :header {:frame_id "/map" :stamp (.subtract (.now *ros*) (Duration. 0.1))}
   :joint_name joint-name :value (if (coll? joint-position) 
				   (vec (map double joint-position)) [(double joint-position)])})

;(def *fk-z-offset*  -0.055  #_0.1141 #_ 0.09412233491155875)

(defn forward-kinematics
  "Returns a lazy seq [in-collision? poses], where poses is a map
   from link names to poses.  Assumes joints in map frame.
   If in_collision is to be accurate, must first publish a collision map
   to the appropriate topic in the fk_node.  Response is corrected to be in map frame.."
 [#^NodeHandle nh joint-map]
   (let [res (call-srv-cached nh "/fk_node/forward_kinematics"
	      (map-msg {:class ForwardKinematics$Request
			:joints (map make-kinematic-joint joint-map)}))
	 [_ base-link] (first 
			(filter (fn [[name pose]] (= name "base_link")) 
				(map vector (:link_names res) (:link_poses res))))
	 z             (:z (:position base-link))
	 offset        (- 0.05 z)]
     (assert base-link)
;     (println res)
     (assert (= (count (:link_names res)) (count (:link_poses res))))
    (cons (> (:in_collision res) 0)
	  (lazy-seq [(apply hash-map 
		      (interleave 
		       (:link_names res) 
		       (for [pose (:link_poses res)]
			 (update-in pose [:position :z] #(+ % offset )))))]))))

(defn robot-forward-kinematics
  "Like forward-kinematics, but takes a robot state and possibly world state,
   if a collision map is to be published."
 ([#^NodeHandle nh robot]
    (forward-kinematics nh (get-joint-map robot)))
 ([#^NodeHandle nh robot world]
    (put-single-message-cached nh "/fk_node/collision_map" 
      (map-msg (world->collision-map world)) )
    (robot-forward-kinematics nh robot)))

(defn object-forward-kinematics
  "Get the current approximate pose (msg) of an object in the gripper, given a robot state."
  [nh right? robot]
  (transform-pose
   (make-pose [0.16 0 0] [0 0 0 1])
   (safe-get* (second (robot-forward-kinematics nh robot))
    (if right? "r_gripper_palm_link" "l_gripper_palm_link"))))

(defn object-fk-point-stamped
  [nh right? robot]
  {:class PointStamped
   :header {:frame_id "/map"}
   :point  (:position (object-forward-kinematics nh right? robot))})


(defn feasible-ik-pose? 
  "Is it physically possible to reach the given pose?  If no, we won't
   bother trying to call IK."
  [right? pose-stamped]
  (let [frame (:frame_id (:header pose-stamped))
	pos (pose-position (:pose pose-stamped))
	[x y z] pos]
;     (println pos (l2-distance [0 0 0] pos))
    (cond (< x 0) 
            nil ;(println "Skipping IK; can't reach behind robot.")
	  (> (l2-distance 
	      (condp = frame "/torso_lift_link" [0 0 0] "/base_link" [0 0 0.9])
	      pos) 0.9)
	    nil ; (println "Skipping IK; can't reach more than 0.9 meters away.")
	  ; ...
          :else true)))

(defn safe-inverse-kinematics 
  "Find an IK solution respecting the collision space.  Pass
   world if you want its collision map published.
   Other initial joint configurations will be randomly generated.
   Returns false for ik invalid, or nil for out of safety/collision limits"
  ([#^NodeHandle nh right? pose-stamped robot world random-retries]
     (safe-inverse-kinematics nh right? pose-stamped robot world random-retries false))
  ([#^NodeHandle nh right? pose-stamped robot world random-retries start-random?]
   (when (feasible-ik-pose? nh pose-stamped) ;; TODO: replace with opt desc.
     (when world
       (put-single-message-cached nh "/fk_node/collision_map" 
	 (map-msg (world->collision-map world)))
       #_ (println "Sent map for FK!"))
     (let [all-joints (get-joint-map robot)]
      (loop [tries random-retries 
	    init-joints (if start-random? (random-arm-joint-map nh right?)
			    (:joint-angle-map ((if right? :rarm :larm) robot)))]
       (let [result
	     (if-let [sol (inverse-kinematics nh right? pose-stamped init-joints)]
	     (let [collision (first (forward-kinematics nh (merge all-joints sol)))
		   safe?     (not (out-of-safety-limits? nh sol))]
	       (println "Found IK solution ..."
			(if collision "" " not ") "in collision," 
			(if safe? "" " not ") "in safety limits.") 
	       (when (and safe? (not collision))
		 sol))
	     (do (println "Failed to find IK solution") false))]
	  (or result
	   (if (> tries 0)
;	      #_ (println "IK failed; retrying with random initial joints.")
	     (recur (dec tries) (random-arm-joint-map nh right?))
	     result))))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Moving the arm unsafely, via trajectory controller ;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-joint-trajectory [init-joints final-joints]
  (assert (= (set (keys init-joints)) (set (keys final-joints))))
  (let [ks (keys init-joints)]
    {:class JointTraj :names ks 
     :points (map (fn [m t] {:positions (map m ks) :time t}) [init-joints final-joints] [0 0.2])}))

 ;; TODO: handle wraparound properly
(defn make-smooth-joint-trajectory [init-joints final-joints step-l2 step-time]
  (assert (= (set (keys init-joints)) (set (keys final-joints))))
  (println "Trying to make smooth trajectory from" init-joints "to" final-joints)
  (let [ks (keys init-joints)
	j1 (map init-joints ks)
	j2 (map final-joints ks)
	jd (map - j2 j1)
	total-dist (arm-l1-distance j1 j2)
	steps (inc (int (/ total-dist step-l2)))
	step-dist (/ total-dist steps)
	step-time (* step-time (/ step-dist step-l2))]
    (println total-dist step-l2 steps step-time)
    {:class JointTraj :names ks 
     :points 
       (for [t (range (inc steps))]
	 {:positions (interpolate-arm-joints j1 j2 (/ t steps))
	    ;(map + j1 (map #(* % (/ t steps)) jd)) 
	  :time (* step-time t)})}))
   

(defonce *good-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Done])))

(defonce *bad-traj-outcomes* 
  (set (map int [TrajectoryQuery$Response/State_Deleted
		 TrajectoryQuery$Response/State_Failed
		 TrajectoryQuery$Response/State_Canceled
		 ])))

(defn start-trajectory [#^NodeHandle nh srv-prefix traj]
  (safe-get*
   (call-srv-cached nh (str srv-prefix "/TrajectoryStart")
      (map-msg TrajectoryStart$Request {:traj traj :hastiming 0 :requesttiming 0}))
   :trajectoryid))
 
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

(defn move-arm-to-state-unsafe 
  ([#^NodeHandle nh arm-state]
     (move-arm-to-state-unsafe nh arm-state 10))
  ([#^NodeHandle nh arm-state wait-secs]
     (move-arm-to-state-unsafe nh arm-state wait-secs 1.0))
  ([#^NodeHandle nh arm-state wait-secs speed-mul]
     (println arm-state)
     (execute-arm-trajectory nh 
       (make-smooth-joint-trajectory (:joint-angle-map (get-current-arm-state nh 
						        (isa? (:class arm-state) ::Right))) 
			      (:joint-angle-map arm-state)
				      0.2 (/ 0.17 speed-mul))
       wait-secs)))

(defn move-arm-to-pose-unsafe
  "Move the gripper to a new pose."
  ([nh right? pose] (move-arm-to-pose-unsafe nh right? pose "/base_link" 10 1.0))
  ([nh right? pose frame timeout speed-mul] 
   (let [ik #_(safe-inverse-kinematics nh right? 
	     {:header {:frame_id frame}
	      :pose   pose} 
	     (get-current-robot-state nh) nil 10)
	    (first 
	      (filter identity
		(take 10 (repeatedly
		 #(inverse-kinematics nh right? 
     	           {:header {:frame_id frame} :pose   pose} 
		  (:joint-angle-map (get-current-arm-state nh right?)))))))]
    (if (not ik) (println "Couldn't find IK solution; not moving")
      (move-arm-to-state-unsafe nh (make-robot-arm-state right? ik) timeout speed-mul)))))


(defn get-arm-pose 
  "Get the current pose of the gripper palm link in the specified frame (base_link by default)."
  ([nh right?] (get-arm-pose nh right? "/base_link"))
  ([nh right? frame]
     (transform-pose-tf nh (str (if right? "r" "l") "_gripper_palm_link") 
			frame [[0 0 0] [0 0 0 1]])))

(defn move-arm-rel-unsafe
  "Move the gripper to a new position relative to the current one, keeping orientation."
  ([nh right? [dx dy dz]] (move-arm-rel-unsafe nh right? [dx dy dz] 10 1.0))
  ([nh right? [dx dy dz] timeout speed-mul] 
   (let [[[x y z] q]  (get-arm-pose nh right? "/torso_lift_link")]
     (move-arm-to-pose-unsafe nh right? 
       {:position {:x (+ x dx) :y (+ y dy) :z (+ z dz)}
	:orientation (make-quaternion q)}
       "/torso_lift_link" timeout speed-mul))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Tuck and untuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn throw-arms [#^NodeHandle nh]
  (doseq [[p id] (doall (for [r? [false true]]
		    (move-arm-to-state-unsafe nh (arm-joint-state r? "up") false)))]
    (wait-for-trajectory nh p id))) 


(defn tuck-arms [#^NodeHandle nh]
  (doseq [[p id] [(move-arm-to-state-unsafe nh (arm-joint-state true "tucked") false)
		(do (Thread/sleep 1000)
		    (move-arm-to-state-unsafe nh (arm-joint-state false "tucked" ) false))]]
    (wait-for-trajectory nh p id)))
  

(defn throw-and-tuck-arms [#^NodeHandle nh]
  (throw-arms nh) (tuck-arms nh))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;; Moving the arm safely, via move_arm ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;	 
     
(def *shared-arm-params*
     {:class KinematicSpaceParameters
      :distance_metric "L2Square" :planner_id      "" :contacts nil
      :volumeMin       {:header {:frame_id "/map"} :point {:x -0.2 :y -1.0 :z 0}}
      :volumeMax       {:header {:frame_id "/map"} :point {:x 100.0 :y 100.0 :z 1.5}}})
(def *larm-params* (assoc *shared-arm-params* :model_id "left_arm"))
(def *rarm-params* (assoc *shared-arm-params* :model_id "right_arm"))

(def *no-constraints* {:class KinematicConstraints :joint_constraint [] :pose_constraint []})

(def *joint-constraint-tolerance* 0.001)

(defn- parse-joint-constraint [[name val]]
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
       :header {:frame_id "/torso_lift_link"}
       :joint_name name
       :value          [value]
       :tolerance_above [tol]
       :tolerance_below [tol]})))

(defn- encode-xyz-pose-constraint-type [x? y? z?]
  (+ (if x? PoseConstraint/POSITION_X 0)
     (if y? PoseConstraint/POSITION_Y 0)
     (if z? PoseConstraint/POSITION_Z 0)))

(defn- encode-rpy-pose-constraint-type [r? p? y?]
  (+ (if r? PoseConstraint/ORIENTATION_R 0)
     (if p? PoseConstraint/ORIENTATION_P 0)
     (if y? PoseConstraint/ORIENTATION_Y 0)))

(defn- encode-pose-constraint-type [[x? y? z?] [roll? pitch? yaw?]]
  (+ (encode-xyz-pose-constraint-type x? y? z?)
     (encode-rpy-pose-constraint-type roll? pitch? yaw?)))

(defn encode-pose-constraint
  "Encode a pose constraint for the gripper, possibly specifying which DOFs to constrain
   (by default, all)."
  ([right? frame [x y z] [ax ay az] angle]
     (encode-pose-constraint right? frame [x y z] [ax ay az] angle [true true true] [true true true]))
  ([right? frame [x y z] [ax ay az] angle [x? y? z?] [roll? pitch? yaw?]]
   (let [tol {:class Point :x 0.01 :y 0.01 :z 0.01}
	 otol {:class Point :x 0.1 :y 0.1 :z 0.1}]
  {:class PoseConstraint :type (encode-pose-constraint-type [x? y? z?] [roll? pitch? yaw?])
   :orientation_importance 0.5
   :position_tolerance_above tol :position_tolerance_below tol
   :orientation_tolerance_above otol :orientation_tolerance_below otol
   :link_name (str (if right? "r" "l") "_gripper_palm_link")
   :pose {:header {:frame_id frame}
	  :pose   {:position    {:x x :y y :z z}
		   :orientation (axis-angle->quaternion-msg [ax ay az] angle)}}})))

(defn upright-gripper-path-constraint [right?]  
  (let [tolv 0.5
	tol {:x tolv :y tolv :z tolv}]
   {:joint_constraint nil
    :pose_constraint 
     [{:type (+ PoseConstraint/ORIENTATION_R PoseConstraint/ORIENTATION_P)
       :link_name (str (if right? "r" "l") "_gripper_palm_link")
       :pose {:header {:frame_id "/base_link"} :pose (make-pose [0 0 0] [0 0 0 1])}
       :orientation_importance 1.0
       :orientation_tolerance_above tol
       :orientation_tolerance_below tol
       :position_tolerance_above tol
       :position_tolerance_below tol}]}))
       

(defn plan-arm-motion
  "Directly call the arm planner to get a feasible trajectory.  
   Joint constraints are passed as map from name to either value,  
   which will use a default tolerance of *joint-constraint-tolerance*, or
   an interval, or an explicit JointConstraint message map.
   Pose constraints are lists of PoseConstraints message maps.
   Init-joints should include base and torso."
  ([#^NodeHandle nh right? world robot-state joint-constraints pose-constraints]
     (plan-arm-motion nh right? world robot-state joint-constraints pose-constraints *no-constraints*))
  ([#^NodeHandle nh right? world robot-state joint-constraints pose-constraints path-constraints]
;  (println "Putting collision map")
  (put-single-message-cached nh "/collision_map_future" (map-msg (world->collision-map world)))
;  (println "Calling plan service")
  (call-srv-cached nh "/future_ompl_planning/plan_kinematic_path"
   (map-msg 
     {:class GetMotionPlan$Request :times 1 :allowed_time 0.5 :planner_id ""
      :params (if right? *rarm-params* *larm-params*)
      :start_state      (doall (map make-kinematic-joint (get-joint-map robot-state)))
      :path_constraints path-constraints
      :goal_constraints {:pose_constraint (vec pose-constraints)
			 :joint_constraint (vec (map parse-joint-constraint joint-constraints))}}))))


(defn describe-motion-plan 
  "Describe a motion plan, as outputted by plan-arm-motion."
  [plan]
  (if (empty? (:states (:path plan)))
      (println "No plan was found")
    (println 
     (str ;(if (:unsafe plan) "unsafe ") 
	  (if (> (:approximate plan) 0) (str "approximate, with distance " (:distance plan) " "))
	  "plan with " (count (:states (:path plan))) " states, time " (last (:times (:path plan)))
	  " found."))))


(defn move-arm-to-state 
  "Actually move arm to state using move_arm action, with replanning, synchronously"
  ([#^NodeHandle nh arm-state] (move-arm-to-state nh arm-state false 60.0))
  ([#^NodeHandle nh arm-state upright? timeout]
     (let [r? (isa? (:class arm-state) ::Right)]
       (run-action nh (str "/move_" (if r? "right" "left") "_arm") MoveArmAction 
	 {:contacts nil
	  :path_constraints  (if upright? (upright-gripper-path-constraint r?) *no-constraints*)
	  :goal_constraints {:pose_constraint  []
			     :joint_constraint (vec (map parse-joint-constraint 
							 (:joint-angle-map arm-state)))}}
	 (Duration. (double timeout))))))

(defn move-arm-to-grasp 
  "Actually move arm to state using move_arm action, with replanning, synchronously"
  ([#^NodeHandle nh arm-state] (move-arm-to-state nh arm-state false 60.0))
  ([#^NodeHandle nh arm-state upright? timeout]
     (let [r? (isa? (:class arm-state) ::Right)]
       (run-action nh (str "/move_" (if r? "right" "left") "_arm") MoveArmAction 
	 {:contacts nil
	  :path_constraints  (if upright? (upright-gripper-path-constraint r?) *no-constraints*)
	  :goal_constraints {:pose_constraint  []
			     :joint_constraint (vec (map parse-joint-constraint 
							 (:joint-angle-map arm-state)))}}
	 (Duration. (double timeout))))))


(defn move-arm-to-pose
  "Move the gripper to a new pose."
  ([nh right? pose] (move-arm-to-pose nh right? pose "/base_link" false 30.0))
  ([nh right? pose frame upright? timeout]
   (let [ik (limited-inverse-kinematics nh right? 
	     {:header {:frame_id frame}
	      :pose   pose} 
	     (:joint-angle-map (get-current-arm-state nh right?))
	     50)]
     (prn ik)
    (if (not ik) (println "Couldn't find IK solution; not moving")
      (move-arm-to-state nh (make-robot-arm-state right? ik) false timeout)))))

;; Old version below: lets move_arm do IK.

#_
(defn move-arm-to-pose
  "Use move_arm to move the gripper to a specific pose." 
  ([nh right? pose] (move-arm-to-pose nh right? pose "/base_link" false 60.0))
  ([nh right? pose frame upright? timeout]
   (let [pos          (decode-point (:position pose))
	 [axis angle] (quaternion-msg->axis-angle (:orientation pose))]			   
    (run-action nh (str "/move_" (if right? "right" "left") "_arm") MoveArmAction
	{:contacts nil
	 :path_constraints  (if upright? (upright-gripper-path-constraint right?) *no-constraints*)
	 :goal_constraints 
	 {:pose_constraint  
	  [(encode-pose-constraint true frame (decode-point (:position pose)) axis angle)]
	  :joint_constraint []}}
	(Duration. (double timeout))))))

(defn move-arm-to-grasp 
  "Actually move arm to state using move_arm action, with replanning, synchronously"
  ([#^NodeHandle nh arm-state] (move-arm-to-state nh arm-state false 60.0))
  ([#^NodeHandle nh arm-state upright? timeout]
     (let [r? (isa? (:class arm-state) ::Right)]
       (run-action nh (str "/move_" (if r? "right" "left") "_arm") MoveArmAction 
	 {:contacts nil
	  :path_constraints  (if upright? (upright-gripper-path-constraint r?) *no-constraints*)
	  :goal_constraints {:pose_constraint  []
			     :joint_constraint (vec (map parse-joint-constraint 
							 (:joint-angle-map arm-state)))}}
	 (Duration. (double timeout))))))

(defn move-arm-to-grasp
  "Use move_arm to move the gripper to a specific grasping pose, which ignores contacts." 
  ([nh right? pose] (move-arm-to-pose nh right? pose "/base_link" false 60.0))
  ([nh right? pose frame upright? timeout]
   (assert (#{"/base_link" "/torso_lift_link"} frame))
   (let [pos          (decode-point (:position pose))
	 [axis angle] (quaternion-msg->axis-angle (:orientation pose))]			   
    (run-action nh (str "/move_" (if right? "right" "left") "_arm") MoveArmAction
	{:contacts 
	  [{:depth 0.04
	    :links (map #(str (if right? "r_gripper_" "l_gripper_") %)
			["l_finger_link" "r_finger_link" "l_finger_tip_link" "r_finger_tip_link" "palm_link"])
	    :pose  {:header {:frame_id frame}
		    :pose   (update-in pose [:position :x] #(+ % 0.1))}
	    :bound {:type ros.pkg.mapping_msgs.msg.Object/SPHERE
		    :dimensions [0.5]
		    :triangles [] :vertices []}}]
	 :path_constraints  (if upright? (upright-gripper-path-constraint right?) *no-constraints*)
	 :goal_constraints 
	 {:pose_constraint  
	  [(encode-pose-constraint true frame (decode-point (:position pose)) axis angle)]
	  :joint_constraint []}}
	(Duration. (double timeout))))))




(defn move-arm-rel 
  "Move the gripper to a new position relative to the current one."
  [nh right? [dx dy dz] upright?]
  (let [current-pose (get-arm-pose nh right?)
	[x y z]      (decode-point (:position current-pose))]
    (move-arm-to-pose nh right?
      (assoc current-pose :position (make-point [(+ x dx) (+ y dy) (+ z dz)]))
      "/base_link" upright? 30.0)))


(defn preempt-arm [nh right?]
  (cancel-action-async  nh (str "/move_" (if right? "right" "left") "_arm")))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;                 Miscellaneous       ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;	 

(defn compute-grasp-pose 
  "Compute a pose for the palm_link to grasp an object at [x y z].
   By default, sets up away from the object, for a straight-ahead grasp."
  ([[x y z]] (compute-grasp-pose [x y z] 0.26 0))
  ([[x y z] dist angle]
     (make-pose 
      [(- x (* dist (Math/cos (double angle))))
       (- y (* dist (Math/sin (double angle))))
       z]
      (decode-quaternion (angle->quaternion angle)))))






















;; For executing prerecoded trajectories
(comment 
(defn read-path-file [f] (map #(read-string (str "[" % "]")) (util/read-lines f)))
(def *drop-traj* (read-path-file "/u/isucan/paths/discard"))
(def *drop-traj2* (read-path-file "/u/isucan/paths/drop_new"))
(def *drop-traj2* (read-path-file "/u/jawolfe/paths/drop_traj3"))
(def *serve-high* (read-path-file "/u/jawolfe/paths/serve_high"))
(def *serve-low* (read-path-file "/u/jawolfe/paths/serve_low"))

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


;TODO: finish, handle wraparound! (also above!)
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
    
(defn do-throw [nh n]
  (let [throw (read-path-file (str "/u/jawolfe/paths/throw" n))]
;    (apply-gripper-force nh true 20)
    (move-arm-directly-to-state nh 
      (make-robot-arm-state true false
       (into {} (map vector *rarm-joints* (first throw)))) 2 100 #_0.3)
    (apply-gripper-force nh true 30)
    (execute-arm-trajectory nh  
      (encode-normalized-arm-trajectory true throw 1000)
      10))) 
  )




