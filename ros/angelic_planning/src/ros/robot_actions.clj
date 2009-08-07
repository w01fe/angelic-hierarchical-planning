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



(ns ros.robot-actions
  (:use   clojure.xml ros.ros ros.world ros.robot ros.geometry)
	  )
  
(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct robot-env  :class :robot :world)

(defn make-robot-env [robot world]
  (struct robot-env ::RobotEnv robot world))

(defn make-current-robot-env 
  ([nh] (make-current-robot-env nh (get-initial-world 0.1 0.1 0)))
  ([nh world] (make-robot-env (get-current-robot-state nh) world)))

(def *base-cost-multiplier* -1)
(def *arm-cost-multiplier* -4)
(def *torso-cost-multiplier* -4)
(def *gripper-cost* -20)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::RobotHLA       ::RobotAction)
(derive ::RobotPrimitive ::RobotAction)

(defmulti robot-primitive-result 
  "Take an action and env and return [new-env step-reward], or nil if impossible"
  (fn [nh action env] (:class action)))

(defmulti execute-robot-primitive 
  "Try to execute this action in the environment, and return true iff succeeded."
  (fn [nh action] (:class action)))

(defmulti robot-action-name :class)

(defmulti robot-action-primitive? :class)
(defmethod robot-action-primitive? ::RobotHLA       [a] false)
(defmethod robot-action-primitive? ::RobotPrimitive [a] true)


(defmulti robot-hla-discrete-refinements? 
  "Are there a finite number of refinements of this HLA?"
  (fn [a] (:class a)))

(defmulti robot-hla-refinements 
  "Return a lazy (often infinite) sequence of immediate refinements."
  (fn [nh a env] (:class a)))

(defmulti sample-robot-hla-refinement
  "Return a single random refinement, or nil for failure."
  (fn [nh a env] (:class a)))


(defmethod robot-hla-refinements ::RobotHLA [nh a env]
  (assert (not (robot-hla-discrete-refinements? a)))
  (filter identity
   (repeatedly #(sample-robot-hla-refinement nh a env)))) ; default implementation

(defmethod sample-robot-hla-refinement ::RobotHLA [nh a env]
  (assert (robot-hla-discrete-refinements? a))
  (let [refs (robot-hla-refinements nh a env)]
    (when (seq refs)
      (nth refs (rand-int (count refs))))))

(defmulti sample-robot-action-primitive-refinement (fn [nh a env] (:class a)))

(defmethod sample-robot-action-primitive-refinement ::RobotHLA [nh a env]
  (if (robot-action-primitive? a) (when (robot-primitive-result nh a env) a)
      (when-let [ref (sample-robot-hla-refinement nh a env)]
	(sample-robot-action-primitive-refinement nh ref env))))

(defn robot-action-primitive-refinements [nh a env max-samples]
;  (println a)
  (if (robot-action-primitive? a) 
      (when (robot-primitive-result nh a env) [a])
    (mapcat #(robot-action-primitive-refinements nh % env max-samples)
	    (if (robot-hla-discrete-refinements? a)
	        (robot-hla-refinements nh a)
	      (filter identity
		(take max-samples 
		  (repeatedly #(sample-robot-hla-refinement nh a env))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Action seqs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::RobotActionSeq    ::RobotAction)
(derive ::RobotPrimitiveSeq ::RobotActionSeq)
(derive ::RobotPrimitiveSeq ::RobotPrimitive)
(derive ::RobotHLASeq ::RobotActionSeq)
(derive ::RobotHLASeq       ::RobotHLA)


(defstruct robot-action-seq :class :actions)

(defn make-robot-action-seq [actions]
  (struct robot-action-seq 
	  (if (every? robot-action-primitive? actions) ::RobotPrimitiveSeq ::RobotHLASeq) 
	  actions))

(defmethod robot-action-name ::RobotActionSeq [a]
  (map robot-action-name (:actions a)))

(defmulti get-action-seq :class)
(defmethod get-action-seq ::RobotAction [a] [a])
(defmethod get-action-seq ::RobotActionSeq [a] (:actions a))

(defmethod robot-primitive-result ::RobotPrimitiveSeq [nh action env]
  (loop [actions (:actions action) env env rew 0]
    (if (empty? actions) [env rew]
      (when-let [[next-env step-rew] (robot-primitive-result nh (first actions) env)]
	(recur (next actions) next-env (+ rew step-rew))))))

(defmethod execute-robot-primitive ::RobotPrimitiveSeq [nh action]
  (doseq [action (:actions action)]
    (execute-robot-primitive nh action)))



(defmethod robot-hla-discrete-refinements? ::RobotHLASeq [a]
  (robot-hla-discrete-refinements?
   (first (filter #(not (robot-action-primitive? %)) (:actions a)))))

(defmethod robot-hla-refinements ::RobotHLASeq [nh a env]
  (loop [pre-actions [] env env post-actions (:actions a)]
    (assert (not (empty? post-actions)))
    (when env
    (if (robot-action-primitive? (first post-actions))
        (recur (conj pre-actions (first post-actions))
	       (first (robot-primitive-result nh (first post-actions) env))
	       (next post-actions))
      (if (not (robot-hla-discrete-refinements? (first post-actions)))
	  (filter identity
	    (repeatedly #(sample-robot-hla-refinement nh a env)))
	(for [ref (robot-hla-refinements nh (first post-actions) env)]
	  (make-robot-action-seq
	   (concat 
	    pre-actions 
	    (get-action-seq ref)
	    (next post-actions)))))))))


(defmethod sample-robot-hla-refinement ::RobotHLASeq [nh a env]
  (loop [pre-actions [] env env post-actions (:actions a)]
    (assert (not (empty? post-actions)))
    (when env
    (if (robot-action-primitive? (first post-actions))
        (recur (conj pre-actions (first post-actions))
	       (first (robot-primitive-result nh (first post-actions) env))
	       (next post-actions))
      (when-let [ref (sample-robot-hla-refinement nh (first post-actions) env)]
	(make-robot-action-seq 
	 (concat 
	  pre-actions 
	  (get-action-seq ref)
	  (next post-actions))))))))

(defn execute-robot-plan [nh actions]
  (execute-robot-primitive nh (make-robot-action-seq actions)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base - Point ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::BaseAction ::RobotPrimitive)

(defstruct base-action :class :goal)

(defn make-base-action [goal]
  (struct base-action ::BaseAction goal))

(defmethod robot-primitive-result ::BaseAction [nh action env]
  (let [sol (plan-base-motion nh (:world env) (:base (:robot env)) (:goal action) [[0 0] [40 40]])]
    (when (seq sol)
      [(assoc-in env [:robot :base] (:goal action)) (* *base-cost-multiplier* 
						       (world-2d-res (:world env))
						       (count sol))])))

(defmethod execute-robot-primitive ::BaseAction [nh action]
  (println "Executing move_base action")
  (move-base-to-state nh (:goal action)))

(defmethod robot-action-name ::BaseAction [a]
  (let [{:keys [x y theta]} (:goal a)]
    ['base-to x y theta]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base - Region ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::BaseRegionAction ::RobotHLA)

(defstruct base-region-action :class :goal-region)

(defn make-base-region-action 
  "Goal-region should be a base-region of some sort"
  [goal-region]
  (struct base-region-action ::BaseRegionAction goal-region))

(defmethod robot-hla-discrete-refinements? ::BaseRegionAction [a] false)

(defmethod sample-robot-hla-refinement ::BaseRegionAction [nh a env]
  (make-base-action (apply make-robot-base-state (sample-region (:goal-region a)))))

(defmethod robot-action-name ::BaseRegionAction [a]
  ['base-to-region (region-name (:goal-region a))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Gripper ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  


(derive ::GripperAction ::RobotPrimitive)

(defstruct gripper-action :class :goal)

(defn make-gripper-action [goal]
  (struct gripper-action ::GripperAction goal))

(defmethod robot-primitive-result ::GripperAction [nh action env]
  (let [field  (if (isa? (:class (:goal action)) :ros.robot/Right) :rgripper :lgripper)
;	was-open? (:open? (field (:robot env)))
;	will-open? (:open (:goal action))
	]
    [(assoc-in env [:robot field] (:goal action))
     *gripper-cost*]))
;     (* *gripper-cost*
;	(if (or (and was-open? (not will-open?)) (and (not was-open?) will-open?)) 1 0))]))
;	(Math/abs (double (- (:separation (:goal action)) (:separation (field (:robot env)))))))]))

(defmethod execute-robot-primitive ::GripperAction [nh action]
  (println "Executing move_gripper action (via actuate gripper action)")
  (move-gripper-to-state nh (:goal action))
  (Thread/sleep 1500))

(defmethod robot-action-name ::GripperAction [a]
  [(if (isa? (:class (:goal a)) :ros.robot/Right) 'right-gripper-to 'left-gripper-to)
   (:open? (:goal a))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Joints  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; Arm joint action simply tries to achieve a robot-arm-state, i.e., set of joint angles.

(derive ::ArmJointAction ::RobotPrimitive)

(defstruct arm-joint-action :class :goal)

(defn make-arm-joint-action [goal]
  (struct arm-joint-action ::ArmJointAction goal))

(defmethod robot-primitive-result ::ArmJointAction [nh action env]
  (let [r?  (isa? (:class (:goal action)) :ros.robot/Right)
	sol (plan-arm-motion nh r? (:world env) (:robot env) (:joint-angle-map (:goal action)) nil)
	times (:times (:path sol))]
    (print "Result for joint action: ") (describe-motion-plan sol)
    (when (> (count times) 0)
      [(assoc-in env [:robot (if r? :rarm :larm)] (:goal action)) 
       (* *arm-cost-multiplier* (last times))])))

;; TODO:use move_arm
;(defmethod execute-robot-primitive ::ArmJointAction [nh action]
;  (println "Executing move_arm action (synchronously, using move_arm)")
;  (move-arm-to-state nh (:goal action)))

(defmethod execute-robot-primitive ::ArmJointAction [nh action]
  (println "Executing move_arm action (synchronously, using trajectory controller)")
  (move-arm-directly-to-state nh (:goal action)))

(defmethod robot-action-name ::ArmJointAction [a]
  (vec
   (cons (if (isa? (:class (:goal a)) :ros.robot/Right) 'right-arm-to 'left-arm-to)
	 (map second (sort-by first (seq (:joint-angle-map (:goal a))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Tuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::TuckArmsAction ::RobotPrimitive)
(derive ::ThrowArmsAction ::RobotPrimitive)

(defn make-tuck-arms-action [] {:class ::TuckArmsAction}) 
(defn make-throw-arms-action [] {:class ::ThrowArmsAction})

;; For now, assume these will always succeed with constant cost, for simplicity
(defonce *tuck-reward* -6)
(defonce *throw-reward* -6)

(defmethod robot-primitive-result ::TuckArmsAction [nh action env]
  [(update-in env [:robot] #(assoc % :rarm *rarm-tucked-state* :larm *larm-tucked-state*))
   *tuck-reward*])
(defmethod robot-primitive-result ::ThrowArmsAction [nh action env]
  [(update-in env [:robot] #(assoc % :rarm *rarm-up-state* :larm *larm-up-state*))
   *throw-reward*])

(defmethod execute-robot-primitive ::TuckArmsAction  [nh action] 
  (println "Tucking arms...")
  (tuck-arms nh))

(defmethod execute-robot-primitive ::ThrowArmsAction [nh action] 
  (println "Throwing arms...")
  (throw-arms nh))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Pose  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempt to move the arm (i.e. palm link to a particular pose

(derive ::ArmPoseAction ::RobotHLA)

(defstruct arm-pose-action :class :right? :pose)

(defn make-arm-pose-action [right? map-gripper-pose]
  (struct arm-pose-action ::ArmPoseAction right? map-gripper-pose))

(defmethod robot-hla-discrete-refinements? ::ArmPoseAction [a] false)

(defmethod sample-robot-hla-refinement ::ArmPoseAction [nh a env]
  (let [r?  (:right? a)
	ik  (safe-inverse-kinematics 
	     nh r? 
	     (map-pose->tll-pose-stamped (:pose a) (:base (:robot env)))
	     (:robot env) (:world env) 0 true)]
    (when ik
      (make-arm-joint-action (make-robot-arm-state r? false ik)))))

(defmethod robot-action-name ::ArmPoseAction [a]
  (vec 
   (cons (if (:right? a) 'right-arm-to-pose 'left-arm-to-pose)
	 (decode-pose (:pose a)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Grasp  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempt to move the arm to a position where a given object can be grasped. 

(derive ::ArmGraspAction ::RobotHLA)

(defstruct arm-grasp-action :class :right? :cx :cy :minz :maxz :radius)

(defn make-arm-grasp-action [right? cx cy minz maxz radius]
  (struct arm-grasp-action ::ArmGraspAction right? cx cy minz maxz radius))

(defmethod robot-hla-discrete-refinements? ::ArmGraspAction [a] false)

(def *grasp-distance* 0.10)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod sample-robot-hla-refinement ::ArmGraspAction [nh a env]
  (let [{:keys [cx cy minz maxz radius]} a
	angle (double (rand-double [0 (* 2 Math/PI)]))
	z     (double (rand-double [minz maxz]))
	slop  0.0 ;(max 0 (- 0.10 radius))
	dist  (double (+ *grasp-distance* (rand-double [(- slop) slop])))]
    (make-arm-pose-action (:right? a)
     {:class ros.pkg.geometry_msgs.msg.Pose
      :position {:x (- cx (* dist (Math/cos angle))) :y  (- cy (* dist (Math/sin angle))) :z z}
      :orientation (angle->quaternion angle)})))
	           
(defmethod robot-action-name ::ArmGraspAction [a]
  (vec 
   (cons (if (:right? a) 'right-arm-to-grasp 'left-arm-to-grasp)
	 [(:cx a) (:cy a) [(:minz a) (:maxz a)]] (:radius a))))

   


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Torso ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; TODO: no collision checking; no integration with map->tll-pose-stamped

(derive ::TorsoAction ::RobotPrimitive)

(defstruct torso-action :class :goal)

(defn make-torso-action [goal]
  (struct torso-action ::TorsoAction goal))

(defmethod robot-primitive-result ::TorsoAction [nh action env]
  [(assoc-in env [:robot :torso] (:goal action))
   (* *torso-cost-multiplier*
      (Math/abs (double (- (:height (:goal action)) (:height (:torso (:robot env)))))))])

(defmethod execute-robot-primitive ::TorsoAction [nh action]
  (println "Executing move_torso action (directly via trajectory controller)")
  (move-torso-to-state nh (:goal action)))

(defmethod robot-action-name ::TorsoAction [a]
  ['torso-to (:height (:goal a))])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; A very dumb search algorithm that just checks all discrete refinements, and 
; samples at most n refinements for each continuous action.  Returns a primitive
; plan + reward.

(defn p [x] (println x) x)

(defn simple-search [nh init-plans env goal-pred max-samples]
  (last 
   (sort-by second
    (for [plan (doall (mapcat #(robot-action-primitive-refinements nh % env max-samples)
		       init-plans))
	  :let [[result rew] (robot-primitive-result nh plan env)]
	  :when (goal-pred result)]
      (p [plan rew])))))
      

(defn get-default-env [nh]
  (make-robot-env (get-current-robot-state nh) (get-initial-world 0.1 0.1 0)))

; (make-robot-action-seq [(make-base-action (make-robot-base-state 20 20 0)) (make-arm-action *larm-up-state*) (make-torso-action (make-robot-torso-state 0.3)) (make-gripper-action (make-robot-gripper-state true 0.05 nil))])
; (:robot (first (robot-primitive-result nh (make-robot-action-seq [(make-base-action (make-robot-base-state 20 20 0)) (make-arm-action *larm-up-state*) (make-torso-action (make-robot-torso-state 0.3)) (make-gripper-action (make-robot-gripper-state true 0.05 nil))]) (make-robot-env (get-current-robot-state nh) (get-initial-world 0.1 0.1 0)))))

; (sample-robot-hla-refinement nh (make-arm-pose-action (encode-pose-constraint true "/torso_lift_link" [0.2 0.6 0.8] [0 0 1] 0)) (make-current-robot-env nh))

; (simple-search nh [(make-arm-pose-action (encode-pose-constraint true "/torso_lift_link" [0.2 0.6 0.8] [0 0 1] 0))] (make-current-robot-env nh) (constantly true) 5)

; (simple-search nh [(make-base-action (make-robot-base-state 25 25 0)) (make-arm-pose-action true (make-pose [25.5 24.8 1.0] [0 0 0 1]))] (get-default-env nh) (constantly true) 3)

(set! *warn-on-reflection* false)










(comment ; Old version, before IK worked
(derive ::ArmPoseAction ::RobotHLA)

(defstruct arm-pose-action :class :pose-constraint)

(defn make-arm-pose-action [pose-constraint]
  (struct arm-pose-action ::ArmPoseAction pose-constraint))

(defmethod robot-hla-discrete-refinements? ::ArmPoseAction [a] false)

(defmethod sample-robot-hla-refinement ::ArmPoseAction [nh a env]
  (let [r?  (.startsWith #^String (:link_name (:pose-constraint a)) "r")
	sol (plan-arm-motion nh r? (:world env) (:robot env) nil [(:pose-constraint a)])]
    (print "Result for pose action: ") (describe-motion-plan sol)
    (when (and (seq (:states (:path sol))));  (not (:approximate sol))) ;TODO ??
      (make-arm-joint-action 
       (make-robot-arm-state r? false
	 (apply hash-map (interleave (:names (:path sol)) (:vals (last (:states (:path sol))))))))))))