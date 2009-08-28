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
  (:import [java.util Random])
  (:use   clojure.xml ros.ros ros.world ros.robot ros.geometry)
	  )
  
(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities for state abstraction ;;;;;;;;;;;;;;;;;;;

(defn merge-deep [m1 m2]
  "Like merge, but deep-merges sub-maps."
  (if (map? m1) 
      (merge-with merge-deep m1 m2)
    m2))

(defn- make-safe [x] (assert x) x)

(defn cherry-pick [schema m]
  "Schema must be a nested map, whose (non-map) leaf values will be ignored.
   Cherry-pick returns the part of m that overlaps with schema."
;  (println "Trying to cherry-pick" schema "from" m)
  (cond (set? schema)
	  (into {} (map #(make-safe (find m %)) schema))
	(map? schema)
	  (into {}
	    (for [[k v] schema]
	      [k (cherry-pick v (get m k))]))
	:else (make-safe m)))
	      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct robot-env  :class :robot :world)

(defn make-robot-env [robot world]
  (struct robot-env ::RobotEnv robot world))

(defn make-current-robot-env 
  ([nh] (make-current-robot-env nh (get-demo-world 0.1 0.1 0)))
  ([nh world] (make-robot-env (get-current-robot-state nh) world)))


;; Cost mulitpliers are intended to make reward approximately negative 
;; execution time, in seconds.

(def *base-cost-multiplier* -2)
(def *base-cost-constant* -20)
(def *base-rel-cost-multiplier* -2)
(def *arm-cost-multiplier* -4)
(def *torso-cost-multiplier* -60)
(def *gripper-cost* -3)

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
  "Return a lazy (often infinite) sequence of immediate refinements. Refinements are seqs of actions."
  (fn [nh a env] (:class a)))


(defmulti sample-robot-hla-refinement-det
  "Return a single random refinement, or nil for failure.  Refinement are seqs of actions.
   As much as possible, results should be deterministic when given the same arguments, 
   by using the supplied java.util.Random to supply randomness."
  (fn [nh a env random] (:class a)))

(def *ra-random*  (Random.))

(defn sample-robot-hla-refinement
  "Return a single random refinement, or nil for failure.  Refinement are seqs of actions."
  [nh a env] (sample-robot-hla-refinement-det nh a env *ra-random*))




(defmethod robot-hla-refinements ::RobotHLA [nh a env]
  (assert (not (robot-hla-discrete-refinements? a)))
  (filter identity
   (repeatedly #(sample-robot-hla-refinement nh a env)))) ; default implementation

(defmethod sample-robot-hla-refinement-det ::RobotHLA [nh a env random]
  (assert (robot-hla-discrete-refinements? a))
  (let [refs (robot-hla-refinements nh a env)]
    (when (seq refs)
      (nth refs (rand-int (count refs))))))


(defmulti robot-action-precondition-context-schema 
  "Optional; like effect-context-schema, for actions
   with a fixed precondition context type"
  (fn [a] (:class a)))

(defmulti robot-action-precondition-context 
  "Return a partial env representing parts of s relevant for 
   preconditions and costs of execiting a from s."
  (fn [a s] (:class a)))

(defmethod robot-action-precondition-context :default [a s]
  (cherry-pick (robot-action-precondition-context-schema a) s))

(defmulti robot-action-effect-context-schema       
  "Return a map representing parts of the env that will be 
   fully controlled by this action. For now, no diff-tracking
   so if something *may* be set it needs to be in prec-context
   as well.  Example: {:robot {:torso true} :world {'bottle' {:on true}}}"
  (fn [a] (:class a)))

(defmethod robot-action-effect-context-schema :default [a] 
  (robot-action-precondition-context-schema a))       


(defn robot-plan-result [nh actions env]
  (loop [actions actions env env rew 0]
    (if (empty? actions) [env rew]
      (when-let [[next-env step-rew] (robot-primitive-result nh (first actions) env)]
	(recur (next actions) next-env (+ rew step-rew))))))

(defn describe-robot-plan [nh actions env]
  (loop [actions actions env env rew 0]
    (if (empty? actions) rew
      (if-let [[next-env step-rew] (robot-primitive-result nh (first actions) env)]
	(do (println "Action" (first actions) "\nhas reward" step-rew "\n")
	    (recur (next actions) next-env (+ rew step-rew)))
	(println "Plan failed at" (first actions))))))

(defn execute-robot-plan  [nh actions]
  (doseq [action actions]
    (execute-robot-primitive nh action)))

(defn execute-robot-plan-handy  [nh actions]
  (wait-for-hand nh)
  (doseq [action actions]
    (let [c (start-hand-counter nh)]
      (execute-robot-primitive nh action)
      (when (> (stop-message-counter nh c) 0)
	(println "Now paused.")
	(wait-for-hand nh)))))

(import-ros)
(defn execute-robot-plan-handy2  [#^NodeHandle nh actions]
  (let [a   (atom false)
	sub (.subscribe nh "/headcart/hands" (ros.pkg.std_msgs.msg.String.) (sub-cb [m] (reset! a true)) 1)]
    (println "Waiting for a hand to start.")
    (while (not @a) (.spinOnce nh)) 
    (Thread/sleep 2000) (.spinOnce nh) (reset! a false)  
    (doseq [action actions]
      (loop []
	(let [f #^java.util.concurrent.Future (future-call #(when (execute-robot-primitive nh action) true))]
	  (while (and (not @a) (not (.isDone f))) (.spinOnce nh))
	  (if @a
	   (do
	    (println "Pausing!")
	    (preempt-base nh)
	    (preempt-arm nh true)
	    (println "Waiting for finish ...")
	    (while (not (.isDone f)) (Thread/sleep 100))
	    (move-arm-to-state nh (arm-joint-state true "tucked"))
	    (.spinOnce nh)
	    (Thread/sleep 2000)
	    (.spinOnce nh)
	    (reset! a false)
	    (println "Waiting for restart signal.")
	    (while (not @a) (.spinOnce nh)) 
	    (Thread/sleep 2000) (.spinOnce nh) (reset! a false)  		
	    (recur))
	  (when (not @f) (throw (Exception.)))))))))

(defn execute-robot-plan-robustly  [nh actions]
  (doseq [action actions]
    (loop []
      (when
        (try (execute-robot-primitive nh action)
	     false
	     (catch Exception e
	       (println "Caught exception" e "; trying again.")
	       (preempt-arm nh true)
	       (preempt-base nh)
	       (move-arm-to-state nh (arm-joint-state true "tucked"))
	       true))
	(recur)))))
	 

(defn execute-robot-plan-hr  [#^NodeHandle nh actions]
  (let [a   (atom false)
	sub (.subscribe nh "/headcart/hands" (ros.pkg.std_msgs.msg.String.) (sub-cb [m] (reset! a true)) 1)]
    (println "Waiting for a hand to start.")
    (while (not @a) (.spinOnce nh)) (reset! a false) 
    (Thread/sleep 2000) (.spinOnce nh) (reset! a false)  
    (doseq [action actions]
      (loop []
	(let [f #^java.util.concurrent.Future
	        (future-call #(try (execute-robot-primitive nh action) false 
				   (catch Exception e (preempt-arm nh true) (preempt-base nh)
					  (println "Caught exception" e "; trying again.")
					  (move-arm-to-state nh (arm-joint-state true "tucked"))
					  true)))]
	  (while (and (not @a) (not (.isDone f))) (.spinOnce nh))
	  (cond  @a
	    (do 
	      (println "Pausing!")
	      (preempt-base nh)
	      (preempt-arm nh true)
	      (println "Waiting for finish ...")
	      (while (not (.isDone f)) (Thread/sleep 100))
	      (move-arm-to-state nh (arm-joint-state true "tucked"))
	      (.spinOnce nh)
	      (Thread/sleep 2000)
	      (.spinOnce nh)
	      (reset! a false)
	      (println "Waiting for restart signal.")
	      (while (not @a) (.spinOnce nh)) (reset! a false)
	      (Thread/sleep 2000) (.spinOnce nh) (reset! a false)  
	      (recur))
	         @f
	      (recur)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base - Point ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::BaseAction ::RobotPrimitive)

(defstruct base-action :class :goal)

(defn make-base-action [goal]
  (struct base-action ::BaseAction goal))

(defmethod robot-primitive-result ::BaseAction [nh action env]
  (track-head nh (base-state->point-stamped (:goal action)))
  (let [sol (plan-base-motion nh (:world env) (:base (:robot env)) (:goal action) [[0 0] [40 40]])]
    (when (seq sol)
      [(assoc-in env [:robot :base] (:goal action)) (+ *base-cost-constant* 
						       (* *base-cost-multiplier* 
						       (world-2d-res (:world env))
						       (count sol)))])))

(defmethod execute-robot-primitive ::BaseAction [nh action]
  (println "Executing move_base action")
  (track-head nh (base-state->point-stamped (:goal action)))
  (assert (= :success (move-base-precise nh (:goal action)))))

(defmethod robot-action-name ::BaseAction [a]
  (let [{:keys [x y theta]} (:goal a)]
    ['base-to x y theta]))

(defmethod robot-action-precondition-context-schema ::BaseAction [a] {:robot #{:base}})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base - Relative ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::BaseRelAction ::RobotPrimitive)

(defstruct base-rel-action :class :coord :dist)

(defn make-base-rel-action [coord dist]
  (assert (#{:x :y} coord))
  (struct base-rel-action ::BaseRelAction coord dist))

(defmethod robot-primitive-result ::BaseRelAction [nh action env]
  (let [[dx dy] (if (= (:coord action) :x) [(:dist action) 0] [0 (:dist action)])
	{:keys [x y theta]} (:base (:robot env))
	theta (double theta) s (Math/sin theta) c (Math/cos theta)]
    [(assoc-in env [:robot :base]
       (make-robot-base-state 
	(+ x (* c dx) (* -1 s dy))
	(+ y (* s dx) (* c dy))
	theta))
     (* (:dist action) *base-rel-cost-multiplier* )]))


(defmethod execute-robot-primitive ::BaseRelAction [nh action]
  (println "Executing move_base_rel action")
  (move-base-rel nh (:coord action) (:dist action)))

(defmethod robot-action-name ::BaseRelAction [a]
  (let [{:keys [coord dist]} (:goal a)]
    ['base-rel coord dist]))

(defmethod robot-action-precondition-context-schema ::BaseRelAction [a] {:robot #{:base}})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Base - Region ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::BaseRegionAction ::RobotHLA)

(defstruct base-region-action :class :goal-region)

(defn make-base-region-action 
  "Goal-region should be a base-region of some sort"
  [goal-region]
  (struct base-region-action ::BaseRegionAction goal-region))

(defmethod robot-hla-discrete-refinements? ::BaseRegionAction [a] false)

(defmethod sample-robot-hla-refinement-det ::BaseRegionAction [nh a env #^Random random]
  (track-head nh (get-xy-theta-region-point-stamped (:goal-region a)))
   [(make-base-action (apply make-robot-base-state (sample-region-det (:goal-region a) random)))])
;  (if (and (< (.nextInt random 5) 1) 
;	   (region-contains? (:goal-region a) (map (:base (:robot env)) [:x :y :theta])))
;     []

(defmethod robot-action-name ::BaseRegionAction [a]
  (println (:goal-region a))
  ['base-to-region (region-name (:goal-region a))])


(defmethod robot-action-precondition-context-schema ::BaseRegionAction [a] {:robot #{:base}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Torso ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; TODO: collision checking; integration with map->tll-pose-stamped

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


(defmethod robot-action-precondition-context-schema ::TorsoAction [a] {:robot #{:torso}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Gripper ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

;; TODO: when grasp fails, ask for help.
(derive ::GripperAction ::RobotPrimitive)

(defstruct gripper-action :class :goal :was-holding)

(defn make-gripper-action 
  ([goal] (make-gripper-action goal nil))
  ([goal was-holding] 
     (assert (or (not was-holding) (not (:holding goal))))
     (struct gripper-action ::GripperAction goal was-holding)))

(defmethod robot-primitive-result ::GripperAction [nh action env]
  (let [right? (isa? (:class (:goal action)) :ros.robot/Right)
	field  (if right? :rgripper :lgripper)
	now-holding (:holding (field (:robot env)))
	will-hold   (:holding (:goal action))
	new-robot   (assoc (:robot env) field (:goal action))
	world       (:world env)
	was-open? (:open? (field (:robot env)))
	will-open? (:open? (:goal action))
	]
    (assert (or (not now-holding) (not will-hold)))
    (assert (= (when now-holding true) (when (:was-holding action) true)))
;    (println "moving gripper; from holding" now-holding "to" will-hold)
;    (println new-robot was-open? will-open?)

    (when will-hold (assert (and was-open? (not will-open?))))
    (when now-holding (assert (and (not was-open?) will-open?)))

    [(make-robot-env new-robot
      (cond now-holding 
  	      (let [obj (safe-get* world now-holding)
		    coord (object-forward-kinematics nh right? new-robot)
		    obj-pt (decode-point (:position coord))
		    surfaces (filter (fn [[n d]] 
				       (when-let [s (:surface d)]
					 (region-contains? s obj-pt)))
				     world)]
		(assert (= (:on obj) "gripper"))
;		(println surfaces obj coord obj-pt)
		(assert (= (count surfaces) 1))
		(let [[surface-name surface-def] (first surfaces)]
		  (assoc world now-holding
		    (assoc obj :on surface-name 
			   :xyz [(first obj-pt) (second obj-pt) (+ (:height surface-def)
								 (/ (:height obj) 2))]))))
	    will-hold 
	      (let [obj (safe-get* world will-hold)]
		(assoc world will-hold
		  (assoc obj :on "gripper" :xyz [0 0 100])))
		    
	    :else      
	      world))
     *gripper-cost*]))
;     (* *gripper-cost*
;	(if (or (and was-open? (not will-open?)) (and (not was-open?) will-open?)) 1 0))]))
;	(Math/abs (double (- (:separation (:goal action)) (:separation (field (:robot env)))))))]))

(defmethod execute-robot-primitive ::GripperAction [nh action]
  (println "Executing move_gripper action (via actuate gripper action)")
  (move-gripper-to-state nh (:goal action))
  (Thread/sleep 3000)
  (when (:holding (:goal action))
    (assert (> (get-current-gripper-separation nh (isa? (:class (:goal action)) :ros.robot/Right)) 0.02))))

(defmethod robot-action-name ::GripperAction [a]
  [(if (isa? (:class (:goal a)) :ros.robot/Right) 'right-gripper-to 'left-gripper-to)
   (:open? (:goal a))])

(defmethod robot-action-precondition-context-schema ::GripperAction [a]
  (let [gripper {:robot #{(if (isa? (:class (:goal a)) :ros.robot/Right) :rgripper :lgripper)}}]
    (cond (:was-holding a)
	    (assoc gripper :world #{(:was-holding a)})
	  (:holding (:goal a))
	    (assoc gripper :world #{(:holding (:goal a))})
	  :else gripper)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Joints  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; Arm joint action simply tries to achieve a robot-arm-state, i.e., set of joint angles.

(derive ::ArmJointAction ::RobotPrimitive)

(defstruct arm-joint-action :class :goal :unsafe?)

(defn make-arm-joint-action 
  ([goal] (make-arm-joint-action goal false))
  ([goal unsafe?]
     (struct arm-joint-action ::ArmJointAction goal unsafe?)))

(defn arm-joint-action-result [nh action env]
  (let [r?  (isa? (:class (:goal action)) :ros.robot/Right)
	final-robot (assoc (:robot env) (if r? :rarm :larm) (:goal action))
	_   (track-head nh (object-fk-point-stamped nh r? final-robot))
	sol (plan-arm-motion nh r? (:world env) (:robot env) (:joint-angle-map (:goal action)) nil)
	times (:times (:path sol))]
    (print "Result for joint action: ") (describe-motion-plan sol)
    (when (> (count times) 0)
      [(assoc env :robot final-robot)
       (* *arm-cost-multiplier* (last times))])))

(defmethod robot-primitive-result ::ArmJointAction [nh action env]
  (first (filter identity (take 3 (repeatedly #(arm-joint-action-result nh action env))))))


;; TODO:use move_arm
;(defmethod execute-robot-primitive ::ArmJointAction [nh action]
;  (println "Executing move_arm action (synchronously, using move_arm)")
;  (move-arm-to-state nh (:goal action)))

(defmethod execute-robot-primitive ::ArmJointAction [nh action]
  (println "Executing move_arm action (synchronously, using move_arm)")
  (track-head nh (object-fk-point-stamped nh (isa? (:class (:goal action)) :ros.robot/Right) (assoc (get-current-robot-state nh) (if (isa? (:class (:goal action)) :ros.robot/Right) :rarm :larm) (:goal action))))
  (if (:unsafe? action)
      (move-arm-to-state-unsafe nh (:goal action))
    (move-arm-to-state nh (:goal action))))

(defmethod robot-action-name ::ArmJointAction [a]
  (vec
   (cons (if (isa? (:class (:goal a)) :ros.robot/Right) 'right-arm-to 'left-arm-to)
	 (map second (sort-by first (seq (:joint-angle-map (:goal a))))))))

(defmethod robot-action-precondition-context-schema ::ArmJointAction [a]
  {:robot #{:base
	    :torso
	    (if (isa? (:class (:goal a)) :ros.robot/Right) :rarm :larm)}})



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Tuck ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::ArmTuckAction ::RobotHLA)

(defstruct arm-tuck-action :class :right?)

(defn make-arm-tuck-action [right?] 
  (struct arm-tuck-action ::ArmTuckAction right?))

(defmethod robot-hla-discrete-refinements? ::ArmTuckAction [a] true)

(defmethod robot-hla-refinements ::ArmTuckAction [nh a env]
  (let [right? (:right? a)
	arm    (if right? :rarm :larm)]	
    (if (:tucked? (arm (:robot env)))
        [[]]
      [[(make-arm-joint-action (arm-joint-state right? "tucked" true))]])))

(defmethod robot-action-name ::ArmTuckAction [a]
  [(if (:right? a) 'tuck-right-arm 'tuck-left-arm)])

(defmethod robot-action-precondition-context-schema ::ArmTuckAction [a]
  {:robot #{(if (:right? a) :rarm :larm)}})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Pose  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempt to move the arm (i.e. palm link) to a particular pose

(derive ::ArmPoseAction ::RobotHLA)

(defstruct arm-pose-action :class :right? :pose :frame)

(defn make-arm-pose-action 
  ([right? map-gripper-pose] (make-arm-pose-action right? map-gripper-pose "/map"))
  ([right? gripper-pose frame]
     (assert (#{"/map" "/base_link"} frame))
     (struct arm-pose-action ::ArmPoseAction right? gripper-pose frame)))

(defmethod robot-hla-discrete-refinements? ::ArmPoseAction [a] false)

(defmethod sample-robot-hla-refinement-det ::ArmPoseAction [nh a env random]
;  (println "TODO: punting on deterministic sampling for arm pose action.")
  (track-head nh {:header {:frame_id (:frame a)} :point (:position (:pose a))})
  (let [r?  (:right? a)
	ik  (safe-inverse-kinematics 
	     nh r? 
	     (condp = (:frame a) 
	       "/map" (map-pose->tll-pose-stamped (:pose a) (:robot env))
	       "/base_link" {:header {:frame_id "/base_link"} :pose (:pose a)})
	     (:robot env) (:world env) 0 true)]
;    (println "Refining arm-pose with pose" (decode-pose (:pose a)) "in frame" (:frame a)
;	     "from" (:base (:robot env)) "got" ik)
    (when ik
      [(make-arm-joint-action (make-robot-arm-state r? ik))])))

(defmethod robot-action-name ::ArmPoseAction [a]
  (vec 
   (cons (if (:right? a) 'right-arm-to-pose 'left-arm-to-pose)
	 (concat (decode-pose (:pose a)) [(:frame a)]))))

(defmethod robot-action-precondition-context-schema ::ArmPoseAction [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Relative Pose  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempt to move the arm (i.e. palm link) by a particular diff, in either  map
; or gripper frame.
;; TODO: fix

(derive ::ArmRelPoseAction ::RobotHLA)

(defstruct arm-rel-pose-action :class :right? :dxyz :gripper?)

(defn make-arm-rel-pose-action 
  ([right? dxyz gripper?]
     (struct arm-rel-pose-action ::ArmRelPoseAction right? dxyz gripper?)))

(defmethod robot-hla-discrete-refinements? ::ArmRelPoseAction [a] true)

(defmethod robot-hla-refinements ::ArmRelPoseAction [nh a env]
  (let [{:keys [right? dxyz gripper?]} a
	gripper-link (if right? "r_gripper_palm_link" "l_gripper_palm_link")
	cur-pose (safe-get* (second (robot-forward-kinematics nh (:robot env)))
			    gripper-link)
	ik  (safe-inverse-kinematics nh right? 
	     (map-pose->tll-pose-stamped 
	      (if gripper?
		(transform-pose (make-pose dxyz [0 0 0 1]) cur-pose)
		(update-in cur-pose [:position] add-points (make-point dxyz))) 
	      (:robot env))
	     (:robot env) (:world env) 0 false)]
    (println "Rel pose action has torso" (:torso (:robot env)) "cur pose" (decode-pose cur-pose))
    (when ik
      [[(make-arm-joint-action (make-robot-arm-state right? ik) true)]])))

;    (println "Relative pose from" dxyz cur-pose gripper?)
	

(defmethod robot-action-name ::ArmRelPoseAction [a]
  [(if (:right? a) 'right-arm-rel-pose 'left-arm-rel-pose)
   (:dxyz a)
   (if (:gripper? a) :gripper :base_link)])

(defmethod robot-action-precondition-context-schema ::ArmRelPoseAction [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Specific Grasp  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempt to move the arm to a position where a given object can be grasped, from a 
; specific angle.  Treated as primitive, because we need perception before going to
; a specific pose.

(def *grasp-approach-distance* 0.26)
(def *grasp-distance* 0.14)
(def *max-object-error* 0.40)

(derive ::ArmGraspAction ::RobotPrimitive)

(defstruct arm-grasp-action :class :right? :obj-map-pt :angle)

(defn make-arm-grasp-action [right? obj-map-pt angle]
  (struct arm-grasp-action ::ArmGraspAction right? obj-map-pt angle))

(defn try-ik-joint-action [nh right? env pose n]
  "Try to do safe IK for a point in map frame, trying at most 
   n times, but failing early if IK invalid.  If succeeds, returns
   an arm-joint-action"
  (let [tll-pose (map-pose->tll-pose-stamped pose (:robot env))]
    (loop [tries 10]
      (let [ik (safe-inverse-kinematics nh right? tll-pose
					(:robot env) (:world env) 0 true)]
	(cond (= ik false) false
	      (= ik nil) (when (> tries 0) (recur (dec tries)))
	      :else [(make-arm-joint-action (make-robot-arm-state right? ik))])))))


(defmethod robot-primitive-result ::ArmGraspAction [nh action env]
  (track-head nh {:header {:frame_id "/map"} :point (make-point (:obj-map-pt action))})
  (let [{:keys [right? obj-map-pt angle]} action
        map->bl-transform  (map->base-link-transform (:base (:robot env))) 
	obj-bl-pt (first (decode-pose (untransform-pose (make-pose obj-map-pt [0 0 0 1]) map->bl-transform)))
	grasp-pose-fn #(transform-pose 
			(compute-grasp-pose obj-bl-pt % angle) 
			map->bl-transform)]
    (println "Trying to refine arm grasp")
    (when-let [ref (try-ik-joint-action nh right? env
		     (grasp-pose-fn *grasp-distance*) 10)]
     (when-let [refp (try-ik-joint-action nh right? env
		      (grasp-pose-fn *grasp-approach-distance*) 10)]
       (when-let [result (robot-primitive-result nh (first ref) env)]
	 (update-in result [1] + 2.0) ; cost for extra movement
	 )))))

(defmethod execute-robot-primitive ::ArmGraspAction [nh action]
  (println "Executing arm-grasp-action...")
  (track-head nh {:header {:frame_id "/map"} :point (make-point (:obj-map-pt action))})
  (move-gripper-to-state nh (make-robot-gripper-state (:right? action) true)) ; make sure open...
  (let [obj (find-specific-object nh (:obj-map-pt action) *max-object-error*)]
    (track-head nh {:header {:frame_id "/base_link"} :point (make-point obj)})
    (assert (= :succeeded 
      (move-arm-to-pose nh (:right? action)
			(compute-grasp-pose obj *grasp-approach-distance* (:angle action))
			"/base_link" false 60.0)))
    (move-arm-to-pose-unsafe nh (:right? action) 
      (compute-grasp-pose obj (/ (+ *grasp-distance* *grasp-approach-distance*) 2) (:angle action))
      "/base_link" 6.0 0.5 #_0.3)
    (move-arm-to-pose-unsafe nh (:right? action) 
      (compute-grasp-pose obj *grasp-distance* (:angle action))
      "/base_link" 6.0 0.3 #_0.3)))

(defmethod robot-action-name ::ArmGraspAction [a]
  ['arm-grasp (:right? a) (:obj-map-pt a) (:angle a)])

(defmethod robot-action-precondition-context-schema ::ArmGraspAction [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)}})



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Grasp  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
; Attempt to move the arm to a position where a given object can be grasped.  
; Height (not yet) and angle for grasp may be unspecified.


(derive ::ArmGraspHLA ::RobotHLA)

(defstruct arm-grasp-hla :class :right? :obj-map-pt :angle-interval)

(defn make-arm-grasp-hla [right? obj-map-pt angle-interval]
  (struct arm-grasp-hla ::ArmGraspHLA right? obj-map-pt angle-interval))

(defmethod robot-hla-discrete-refinements? ::ArmGraspHLA [a] false)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod sample-robot-hla-refinement-det ::ArmGraspHLA [nh a env random]
  (track-head nh {:header {:frame_id "/map"} :point (make-point (:obj-map-pt a))})
  (let [{:keys [right? obj-map-pt angle-interval]} a]
    [(make-arm-grasp-action right? obj-map-pt (sample-region-det angle-interval random))]))
	           
(defmethod robot-action-name ::ArmGraspHLA [a]
  ['arm-grasp (:right? a) (:obj-map-pt a) (:interval (:angle-interval a))])


(defmethod robot-action-precondition-context-schema ::ArmGraspHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Drop  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
; Attempt to move the arm to a position where a given object can be dropped.  


(derive ::ArmDropHLA ::RobotHLA)

(defstruct arm-drop-hla :class :right? :obj-map-pt :drop-torso-height :map-angle-interval)

(defn make-arm-drop-hla [right? obj-map-pt drop-height map-angle-interval]
  (struct arm-drop-hla ::ArmDropHLA right? obj-map-pt drop-height map-angle-interval))

(defmethod robot-hla-discrete-refinements? ::ArmDropHLA [a] false)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod sample-robot-hla-refinement-det ::ArmDropHLA [nh a env random]
  (track-head nh {:header {:frame_id "/map"} :point (make-point (:obj-map-pt a))})
  (println "Drop for" (:obj-map-pt a) (:drop-torso-height a))
  (let [{:keys [right? obj-map-pt map-angle-interval]} a]
    (try-ik-joint-action nh right?
      (assoc-in env [:robot :torso :height] (:drop-torso-height a))
      (compute-grasp-pose obj-map-pt *grasp-distance* 
		     (sample-region-det map-angle-interval random))
      10)))
	      

	           
(defmethod robot-action-name ::ArmDropHLA [a]
  ['arm-drop (:right? a) (:obj-map-pt a) (:drop-torso-height a) (:interval (:map-angle-interval a))])


(defmethod robot-action-precondition-context-schema ::ArmDropHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper; Pickup  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::GraspHLA ::RobotHLA)

(defstruct grasp-hla :class :right? :obj-name)

(defn make-grasp-hla [right? obj-name]
  (struct grasp-hla ::GraspHLA right? obj-name))


(defmethod robot-hla-discrete-refinements? ::GraspHLA [a] true)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod robot-hla-refinements ::GraspHLA [nh a env]
  (let [{:keys [right? obj-name]} a]
    [[(make-arm-grasp-hla right? 
	(:xyz (safe-get* (:world env) obj-name)) 
	(make-interval-region [(/ Math/PI -4) (/ Math/PI 4)]))
      (make-gripper-action 
       (make-robot-gripper-state right? false 60 obj-name))
      (make-torso-action (make-robot-torso-state 0.19))
      ;(make-arm-joint-action (arm-joint-state right? "home"))
      ; (make-arm-rel-pose-action right? [-0.1 0 0.00] true)
     ; (make-arm-joint-action (arm-joint-state right? "home"))
      ]]))
	           
(defmethod robot-action-name ::GraspHLA [a]
  ['grasp (:right? a) (:obj-name a)])

(defmethod robot-action-precondition-context-schema ::GraspHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})


;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper + Base; Pickup  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn compute-base-grasp-region 
  "Given a world and object, compute a good base region for pickup.   
   Return nil if no pose is thought feasible."
  [map-pt table]
  (let [[x y _]  map-pt
	[[minx maxx] [miny maxy]] (get-xy-region-extent (:surface table))]
    (assert (and (<= minx x maxx) (<= miny y maxy)))
    (let [miny? (< (Math/abs (double (- miny y))) (Math/abs (double (- maxy y))))
	  [diry edgey] (if miny? [-1 miny] [1 maxy])
	  disty        (Math/abs (double (- edgey y)))      
          minx? (< (Math/abs (double (- minx x))) (Math/abs (double (- maxx x))))
	  [dirx edgex] (if minx? [-1 minx] [1 maxx])
	  distx        (Math/abs (double (- edgex x)))
	  x?           (< distx disty)]
      (when (< (min distx disty) 0.3)
	(if (not x?)
	  (make-xytheta-region
	   [(- x 0.4) (+ x 0.4)]
	   (sort [(+ y (* diry 0.90)) (+ edgey (* diry 0.60))])
	   [(+ (* Math/PI 0.9 0.5) (if miny? 0 Math/PI)) (+ (* Math/PI 1.1 0.5) (if miny? 0 Math/PI))])
	  (make-xytheta-region
	   (sort [(+ x (* dirx 0.90)) (+ edgex (* dirx 0.60))])
	   [(- y 0.6) (+ y 0.6)]
	   [(+ (* -0.05 Math/PI) (if minx? 0 Math/PI)) (+ (* 0.05 Math/PI) (if minx? 0 Math/PI))]))))))
	  
	   ;(make-robot-base-state (- x (* dir 0.1)) (+ y (* dir 1.0)) ))))

(derive ::GoGraspHLA ::RobotHLA)

(defstruct go-grasp-hla :class :right? :obj-name)

(defn make-go-grasp-hla [right? obj-name]
  (struct go-grasp-hla ::GoGraspHLA right? obj-name))

(defmethod robot-hla-discrete-refinements? ::GoGraspHLA [a] true)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod robot-hla-refinements ::GoGraspHLA [nh a env]
  (let [{:keys [right? obj-name]} a
	world (:world env)
	obj (safe-get* world obj-name)
	base-region (compute-base-grasp-region (:xyz obj) (safe-get* world (:on obj)))]
    (if base-region
      (concat 
       (when (region-contains? base-region (map (:base (:robot env)) [:x :y :theta]))
	 [[(make-arm-tuck-action right?)
	   (make-grasp-hla right? obj-name)]])
       [[(make-arm-tuck-action right?)
	 (make-base-region-action base-region)
	 (make-grasp-hla right? obj-name)]])
      (println "Could not find base region to grasp" obj-name))))
	           
(defmethod robot-action-name ::GoGraspHLA [a]
  ['go-grasp (:right? a) (:obj-name a)])
  
(defmethod robot-action-precondition-context-schema ::GoGraspHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper; Putdown (point)  ;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::DropHLA ::RobotHLA)

(defstruct drop-hla :class :right? :obj-name :map-pt)

(defn make-drop-hla [right? obj-name map-pt]
  (struct drop-hla ::DropHLA right? obj-name map-pt))


(defmethod robot-hla-discrete-refinements? ::DropHLA [a] true)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod robot-hla-refinements ::DropHLA [nh a env]
  (let [{:keys [right? map-pt]} a
	base-theta (:theta (:base (:robot env)))]
    [[(make-arm-drop-hla right? 
	(update-in map-pt [2] + 0.00) ;map-pt 
	0.05
;	(update-in map-pt [2] + 0.18)
	(make-interval-region [(- base-theta 1) (+ base-theta 1)]))
      (make-torso-action (make-robot-torso-state 0.05))
      (make-gripper-action 
       (make-robot-gripper-state right? true)
       (safe-get* ((if right? :rgripper :lgripper) (:robot env)) :holding))
      (make-arm-rel-pose-action right? [-0.1 0 0.2] true)
      ]]))
	           
(defmethod robot-action-name ::DropHLA [a]
  ['drop (:right? a) (:map-pt a)])

(defmethod robot-action-precondition-context-schema ::DropHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})


;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper + Base; Drop  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(derive ::GoDropHLA ::RobotHLA)

(defstruct go-drop-hla :class :right? :obj-name :table-name :map-pt)

(defn make-go-drop-hla [right? obj-name table-name map-pt]
  (struct go-drop-hla ::GoDropHLA right? obj-name table-name map-pt))

(defmethod robot-hla-discrete-refinements? ::GoDropHLA [a] true)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod robot-hla-refinements ::GoDropHLA [nh a env]
  (let [{:keys [right? map-pt obj-name table-name]} a
	base-region (compute-base-grasp-region map-pt (safe-get* (:world env) table-name))]
    (if base-region
      [[(make-drop-hla right? obj-name map-pt)]
       [(make-arm-tuck-action right?)
	(make-base-region-action base-region)
        (make-drop-hla right? obj-name map-pt)]]
     (println "Could not find base region for map-pt" map-pt))))
	           
(defmethod robot-action-name ::GoDropHLA [a]
  ['go-drop (:right? a) (:obj-name a) (:table-name a) (:map-pt a)])
  
(defmethod robot-action-precondition-context-schema ::GoDropHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})



;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper + Base; Drop Region  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::GoDropRegionHLA ::RobotHLA)

(defstruct go-drop-region-hla :class :right? :obj-name :table-name :drop-region)

(defn make-go-drop-region-hla [right? obj-name table-name drop-region]
  (struct go-drop-region-hla ::GoDropRegionHLA right? obj-name table-name drop-region))

(defmethod robot-hla-discrete-refinements? ::GoDropRegionHLA [a] false)

(defmethod sample-robot-hla-refinement-det ::GoDropRegionHLA [nh a env random]
   [(make-go-drop-hla (:right? a) (:obj-name a) (:table-name a) 
		      (conj (vec (sample-region-det (:drop-region a) random)) 
			    (+ 0.20 (:height (safe-get* (:world env) (:table-name a))))))])
	           
(defmethod robot-action-name ::GoDropRegionHLA [a]
  ['go-drop-region (:right? a) (:obj-name a) (:table-name a) (region-name (:drop-region a))])
  
 (defmethod robot-action-precondition-context-schema ::GoDropRegionHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})


;;;;;;;;;;;;;;;;;;;;;;;;;; Arm+ Gripper + Base; Move  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::MoveToGoalHLA ::RobotHLA)

(defstruct move-to-goal-hla :class :right? :obj-name)

(defn make-move-to-goal-hla [right? obj-name]
  (struct move-to-goal-hla ::MoveToGoalHLA right? obj-name))

(defmethod robot-hla-discrete-refinements? ::MoveToGoalHLA [a] true)

;; TODO: use base pose of robot to assist in sampling feasible poses.
(defmethod robot-hla-refinements ::MoveToGoalHLA [nh a env]
  (let [[table drop-region] (:goal (safe-get* (:world env) (:obj-name a)))]
    [[(make-go-grasp-hla (:right? a) (:obj-name a))
      (make-go-drop-region-hla  (:right? a) (:obj-name a) table drop-region)]]))
	           
(defmethod robot-action-name ::MoveToGoalHLA [a]
  ['move-to-goal (:right? a) (:obj-name a)])
  
(defmethod robot-action-precondition-context-schema ::MoveToGoalHLA [a]
  {:robot #{:base
	    :torso
	    (if (:right? a) :rarm :larm)
	    (if (:right? a) :rgripper :lgripper)}
   :world #{(:obj-name a)}})  


;;;;;;;;;;;;;;;;;;;;;;;;;; Enforce goal satisfaction  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fake primitive action that just verifies that object goal was achieved, and removes goal.

(derive ::EnforceGoalAction ::RobotPrimitive)

(defstruct enforce-goal-action :class :obj-name)

(defn make-enforce-goal-action [obj-name]
  (struct enforce-goal-action ::EnforceGoalAction obj-name))

(defmethod robot-primitive-result ::EnforceGoalAction [nh action env]
  (let [obj-name (:obj-name action)
	obj      (safe-get* (:world env) obj-name)
	[goal-table goal-region] (:goal obj)]
    (assert (= goal-table (:on obj)))
    (assert (region-contains? goal-region (drop-last 1 (:xyz obj))))
    [(assoc-in env [:world obj-name :goal] nil) 0]))

(defmethod execute-robot-primitive ::EnforceGoalAction [nh action] true)
	           
(defmethod robot-action-name ::EnforceGoalAction [a]
  ['enforce-goal (:right? a) (:obj-name a)])
  
(defmethod robot-action-precondition-context-schema ::EnforceGoalAction [a]
  {:world #{(:obj-name a)}})  




;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level action  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here, we use the invariant that goals are only present if not alreay satisfied.
;; This Act is for single-arm robots.

(derive ::ActHLA ::RobotHLA)

(defstruct act-hla :class :right?)

(defn make-act-hla [right?]
  (struct act-hla ::ActHLA right?))

(defmethod robot-hla-discrete-refinements? ::ActHLA [a] true)

(defmethod robot-hla-refinements ::ActHLA [nh a env]
  (let [remaining-objects
	  (for [[obj-name {goal :goal}] (:world env)
		:when goal]
	    obj-name)]
    (if (empty? remaining-objects)
        [[]]
      (for [obj remaining-objects]
	[(make-move-to-goal-hla (:right? a) obj)
	 (make-enforce-goal-action obj)
	 a]))))
	           
(defmethod robot-action-name ::ActHLA [a]
  ['act])
  
(defmethod robot-action-precondition-context-schema ::ActHLA [a]
  #{:robot 
    :world})



;;;;;;;;;;;;;;;;;;;;;;;;;; Setup action  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; make sure the robot is in a good state to start planning

(derive ::SetupHLA ::RobotHLA)

(defstruct setup-hla :class :arms)

(defn make-setup-hla [arms]
  (struct setup-hla ::SetupHLA arms))

(defmethod robot-hla-discrete-refinements? ::SetupHLA [a] true)

(defmethod robot-hla-refinements ::SetupHLA [nh a env]
  [(apply concat
    (for [right? (:arms a)]
      [(make-gripper-action (make-robot-gripper-state right? true))
       (make-arm-tuck-action right?)]))])
	           
(defmethod robot-action-name ::SetupHLA [a]
  ['setup (:arms a)])
  
(defmethod robot-action-precondition-context-schema ::SetupHLA [a]
  #{:robot 
    :world})





;; TODO: act, satisfy goal


(set! *warn-on-reflection* false)



(defn get-default-env [nh]
  (make-robot-env (get-current-robot-state nh) (get-demo-world 0.1 0.1 0)))

(defn get-default-lowrez-env [nh]
  (make-robot-env (get-current-robot-state nh) (get-demo-world 1 1 0)))

;; Stuff below not currently in use.  

















;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  

; A very dumb search algorithm that just checks all discrete refinements, and 
; samples at most n refinements for each continuous action.  Returns a primitive
; plan + reward.

(comment 
(defn p [x] (println x) x)

(defn simple-search [nh init-plans env goal-pred max-samples]
  (last 
   (sort-by second
    (for [plan (doall (mapcat #(robot-action-primitive-refinements nh % env max-samples)
		       init-plans))
	  :let [[result rew] (robot-primitive-result nh plan env)]
	  :when (goal-pred result)]
      (p [plan rew])))))
      



 )
; (make-robot-action-seq [(make-base-action (make-robot-base-state 20 20 0)) (make-arm-action *larm-up-state*) (make-torso-action (make-robot-torso-state 0.3)) (make-gripper-action (make-robot-gripper-state true 0.05 nil))])
; (:robot (first (robot-primitive-result nh (make-robot-action-seq [(make-base-action (make-robot-base-state 20 20 0)) (make-arm-action *larm-up-state*) (make-torso-action (make-robot-torso-state 0.3)) (make-gripper-action (make-robot-gripper-state true 0.05 nil))]) (make-robot-env (get-current-robot-state nh) (get-initial-world 0.1 0.1 0)))))

; (sample-robot-hla-refinement nh (make-arm-pose-action (encode-pose-constraint true "/torso_lift_link" [0.2 0.6 0.8] [0 0 1] 0)) (make-current-robot-env nh))

; (simple-search nh [(make-arm-pose-action (encode-pose-constraint true "/torso_lift_link" [0.2 0.6 0.8] [0 0 1] 0))] (make-current-robot-env nh) (constantly true) 5)

; (simple-search nh [(make-base-action (make-robot-base-state 25 25 0)) (make-arm-pose-action true (make-pose [25.5 24.8 1.0] [0 0 0 1]))] (get-default-env nh) (constantly true) 3)












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
       (make-robot-arm-state r? 
	 (apply hash-map (interleave (:names (:path sol)) (:vals (last (:states (:path sol))))))))))))



(comment ; Old stuff, prior to integration with angelic code. 
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

)




(comment 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Arm - Tuck  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::TuckArmsAction ::RobotPrimitive)
(derive ::ThrowArmsAction ::RobotPrimitive)

(defn make-tuck-arms-action [] {:class ::TuckArmsAction}) 
(defn make-throw-arms-action [] {:class ::ThrowArmsAction})

;; For now, assume these will always succeed with constant cost, for simplicity
(defonce *tuck-reward* -6)
(defonce *throw-reward* -6)

(defmethod robot-primitive-result ::TuckArmsAction [nh action env]
  [(update-in env [:robot] 
	      #(assoc % :rarm (arm-joint-state true "tucked" true)
		        :larm (arm-joint-state false "tucked" true)))
   *tuck-reward*])
(defmethod robot-primitive-result ::ThrowArmsAction [nh action env]
  [(update-in env [:robot] 
	      #(assoc % :rarm (arm-joint-state true "up")
		        :larm (arm-joint-state true "up")))
   *throw-reward*])

(defmethod execute-robot-primitive ::TuckArmsAction  [nh action] 
  (println "Tucking arms...")
  (tuck-arms nh))

(defmethod execute-robot-primitive ::ThrowArmsAction [nh action] 
  (println "Throwing arms...")
  (throw-arms nh))

)