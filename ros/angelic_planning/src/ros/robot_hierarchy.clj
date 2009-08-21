;///////////////////////////////////////////////////////////////////////////////
;// Robot hierarchy, bridges  planning code and robot-actions.clj
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



(ns ros.robot-hierarchy
  (:require
   [ros.robot :as robot] [ros.robot-actions :as ra]
   [edu.berkeley.ai [util :as util] [envs :as envs]] 
   [edu.berkeley.ai.angelic :as angelic]
   [edu.berkeley.ai.angelic.hierarchies :as hierarchies])
  )
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Abstract state, robot, env  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defstruct abstract-robot-base-state    :class :base-region)

(defn make-abstract-robot-base-state [base-region]
  (struct abstract-robot-base-state ::AbstractBaseState base-region))


(defstruct abstract-robot-arm-state :class)



(derive ::AbstractLeftArmState ::AbstractArmState)
(derive ::AbstractLeftArmState ::robot/Left)
(derive ::AbstractRightArmState ::AbstractArmState)
(derive ::AbstractRightArmState ::robot/Right)

(defn make-abstract-robot-arm-state [right?]
  (struct abstract-robot-arm-state (if right? ::AbstractRightArmState ::AbstractLeftArmState)))


(defn make-abstract-robot-state [base torso larm rarm lgripper rgripper]
  (struct robot/robot-state ::AbstractRobotState base torso larm rarm lgripper rgripper))

(defn robot-state->abstract-robot-state [s]
  (assoc s :class ::AbstractRobotState))





(defn make-abstract-robot-env [robot world]
  (struct ra/robot-env ::AbstractRobotEnv robot world))



; Wrapper for env defined in robot-env.
; Environment is just a robot-env 

; Punt on action space for now
(defn make-dummy-action-space []
  {:class ::DummyActionSpace})


(defn make-angelic-robot-env [robot-env]
  (envs/make-environment
   robot-env
   (envs/make-state-set str)
   (make-dummy-action-space)
   (constantly true)))
   ; TODO: proper goal pred
;   (envs/make-simple-condition goal-pred true)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Valuations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-abstract-robot-valuation 
  "An abstract-robot-valuations is a map from abstract-robot-envs to rewards."
  [abstract-env-map]
  (if (empty? abstract-env-map)
      angelic/*pessimal-valuation*
    {:class ::AbstractRobotValuation :abstract-env-map abstract-env-map}))

(derive ::AbstractRobotValuation ::angelic/Valuation)

(defmethod angelic/valuation-max-reward ::AbstractRobotValuation [val]
  (apply max (vals (:abstract-env-map val))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   


(defstruct angelic-robot-action :class :robot-action :hierarchy)

(defn make-angelic-robot-action [robot-action hierarchy]
  (struct angelic-robot-action ::AngelicRobotAction robot-action hierarchy))

(derive ::AngelicRobotTLA ::AngelicRobotAction)
(defn make-angelic-top-level-robot-action [initial-plans hierarchy]
  {:class ::AngelicRobotTLA :initial-plans initial-plans :hierarchy hierarchy})

(derive ::AngelicRobotFinish ::AngelicRobotAction)
(defn make-angelic-finish-action [goal-pred hierarchy]
  {:class ::AngelicRobotFinish :goal-pred goal-pred :hierarchy hierarchy
   :description {:class ::RobotFinishDescription :goal-pred goal-pred}})



(defn make-angelic-robot-hierarchy 
  "Goal-pred should work on either abstract or concrete env."
  [nh initial-plans env sample-depths]
  (let [h {:class ::AngelicRobotHierarchy 
	   :nh nh :angelic-env (make-angelic-robot-env env) 
	   :sample-depths sample-depths}]
    [(make-angelic-top-level-robot-action initial-plans h)
     (make-angelic-finish-action (constantly true) h)]))
 ;; TODO: real goal.


(defmethod hierarchies/hla-primitive? ::AngelicRobotAction [hla]
  (ra/robot-action-primitive? (:robot-action hla)))

(defmethod hierarchies/hla-primitive? ::AngelicRobotTLA [a] false )
(defmethod hierarchies/hla-primitive? ::AngelicRobotFinish [a] true)


(defmethod hierarchies/hla-primitive ::AngelicRobotAction [hla]
  (assert (ra/robot-action-primitive? (:robot-action hla)))
  (:robot-action hla))

(defmethod hierarchies/hla-primitive ::AngelicRobotFinish [a] :noop)


(defmethod hierarchies/hla-environment ::AngelicRobotAction [a]
  (:angelic-env (:hierarchy a)))


(defmethod hierarchies/hla-default-optimistic-valuation-type  ::AngelicRobotAction [hla]
  ::angelic/ExplicitValuation)

(defmethod hierarchies/hla-default-pessimistic-valuation-type ::AngelicRobotAction [hla]
  ::angelic/ExplicitValuation)


(defmethod hierarchies/hla-name ::AngelicRobotAction       [hla] 
;  (println hla)
;  (println (:robot-action hla))
  (ra/robot-action-name (:robot-action hla)))
(defmethod hierarchies/hla-name ::AngelicRobotTLA    [hla] '[top-level])
(defmethod hierarchies/hla-name ::AngelicRobotFinish [hla] '[finish])


(defmethod hierarchies/hla-hierarchical-preconditions ::AngelicRobotAction [hla] 
  envs/*true-condition*)


(defmethod hierarchies/hla-immediate-refinements [::AngelicRobotAction ::angelic/ExplicitValuation]
  [hla opt-val]
  (let [a (:robot-action hla)
	h (:hierarchy hla)
	[env rew-so-far] (util/safe-singleton (angelic/explicit-valuation-map opt-val))]
    (assert (= (:class env) ::ra/RobotEnv))
    (println "Refining" (hierarchies/hla-name hla))
    (for [plan 
	  (if (ra/robot-hla-discrete-refinements? a)
	    (ra/robot-hla-refinements (:nh h) a env)
	    (let [num-refs (util/safe-get (:sample-depths h) (:class a))]
	      (filter identity
		      (take num-refs
			    (repeatedly #(ra/sample-robot-hla-refinement (:nh h) a env))))))]
      (for [action plan]
	(do 
;	  (println (:class action))
	  (make-angelic-robot-action action h))))))
      
(defmethod hierarchies/hla-immediate-refinements [::AngelicRobotTLA ::angelic/ExplicitValuation]
  [hla opt-val]
  (let [h (util/safe-get hla :hierarchy)]
    (for [plan (util/safe-get hla :initial-plans)]
      (for [action plan]
	(do 
;	  (println (:class action))
	(make-angelic-robot-action action h))))))

;(defmethod hierarchies/hla-immediate-refinements [::AngelicRobotFinish ::angelic/Valuation]
;  [hla opt-val]
;  nil)

(defn- make-primitive-description [hla]
  {:class ::RobotPrimitiveDescription :hla hla})

(defmethod angelic/progress-valuation [::angelic/PessimalValuation ::RobotPrimitiveDescription] [val desc]
  angelic/*pessimal-valuation*)

(defmethod angelic/progress-valuation [::angelic/ExplicitValuation ::RobotPrimitiveDescription]
  [val desc]
  (let [hla (:hla desc)
	a (:robot-action hla)
	h (:hierarchy hla)
	[env rew-so-far] (util/safe-singleton (angelic/explicit-valuation-map val))]
    (assert (= (:class env) ::ra/RobotEnv))
    (if-let [[next-env step-rew] (ra/robot-primitive-result (:nh h) a env)]
        (angelic/make-explicit-valuation {next-env (+ rew-so-far step-rew)})
      angelic/*pessimal-valuation*)))

;; TODO !!
(defmethod angelic/progress-valuation [::angelic/ConditionalValuation ::RobotPrimitiveDescription] [val desc]
  val)


(defmethod angelic/progress-valuation [::angelic/PessimalValuation ::RobotFinishDescription] [val desc]
  angelic/*pessimal-valuation*)

(defmethod angelic/progress-valuation [::angelic/ExplicitValuation ::RobotFinishDescription]
  [val desc]
  (let [goal-pred (:goal-pred desc) 
	[env rew-so-far] (util/safe-singleton (angelic/explicit-valuation-map val))]
    (if (goal-pred env)
        (angelic/make-explicit-valuation {angelic/*finish-state* rew-so-far})
      angelic/*pessimal-valuation*)))

(defmethod angelic/progress-valuation [::angelic/ConditionalValuation ::RobotFinishDescription]
  [val desc]
  (assert (= (:condition val) envs/*true-condition*))
  (angelic/make-explicit-valuation {angelic/*finish-state* (angelic/valuation-max-reward val)}))






(defmethod hierarchies/hla-optimistic-description ::AngelicRobotAction [hla]
  (let [a (:robot-action hla)]
    (if (isa? (:class a) ::ra/RobotPrimitive)
        (make-primitive-description hla)
      (angelic/make-optimal-description))))

(defmethod hierarchies/hla-pessimistic-description ::AngelicRobotAction [hla]
  (let [a (:robot-action hla)]
    (if (isa? (:class a) ::ra/RobotPrimitive)
        (make-primitive-description hla)
      angelic/*pessimal-description*)))

(defmethod hierarchies/hla-optimistic-description ::AngelicRobotTLA [hla]
  (angelic/make-optimal-description))

(defmethod hierarchies/hla-pessimistic-description ::AngelicRobotTLA [hla]
  angelic/*pessimal-description*)

(defmethod hierarchies/hla-optimistic-description ::AngelicRobotFinish [hla]
  (:description hla))

(defmethod hierarchies/hla-pessimistic-description ::AngelicRobotFinish [hla]
  (:description hla))





(comment 

 (aha-star-search (alt-node (make-angelic-robot-hierarchy nh [[(make-base-region-action (make-xytheta-region [26.5 27.3] [25 26] [0 (* 2 Math/PI)])) (make-arm-pose-action false (make-pose [27.43 25.44 0.7] [0 0 0 1]))]] (get-default-env nh) (constantly true) {:ros.robot-actions/BaseRegionAction 10 :ros.robot-actions/ArmPoseAction 5}) {:graph? false :cache? false :ref-choice-fn first-choice-fn}))

 (aha-star-search (alt-node (make-angelic-robot-hierarchy nh [[(make-base-region-action (make-xytheta-region [16 17] [25 26] [0 (* 2 Math/PI)])) (make-grasp-hla false "bottle")]] (get-default-env nh) {:ros.robot-actions/BaseRegionAction 10 :ros.robot-actions/ArmGraspHLA 5}) {:graph? false :cache? false :ref-choice-fn first-choice-fn}))

 (aha-star-search (alt-node (make-angelic-robot-hierarchy nh [[(make-gripper-action (make-robot-gripper-state false true)) (make-base-region-action (make-xytheta-region [16 17] [25 26] [0 (* 2 Math/PI)])) (make-grasp-hla false "bottle")]] (get-default-env nh) {:ros.robot-actions/BaseRegionAction 10 :ros.robot-actions/ArmGraspHLA 5}) {:graph? false :cache? false :ref-choice-fn first-choice-fn}))

  (aha-star-search (alt-node (make-angelic-robot-hierarchy nh [[(make-gripper-action (make-robot-gripper-state false true)) (make-base-region-action (make-xytheta-region [15.6 16] [25 27] [0 (* 2 Math/PI)])) (make-grasp-hla false "bottle") (make-drop-hla false [16.2 26.3 0.85])]] (get-default-env nh) {:ros.robot-actions/BaseRegionAction 10  :ros.robot-actions/ArmGraspHLA 5  :ros.robot-actions/ArmDropHLA 5  :ros.robot-actions/ArmPoseAction 1 }) {:graph? false :cache? false :ref-choice-fn first-choice-fn}))
 )