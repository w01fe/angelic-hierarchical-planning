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

(defmsgs [mechanism_msgs    MechanismState])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Whole robot state info ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defonce *robot-xml* nil)
(defonce *robot-joint-limits* nil)
(defonce *robot-safe-joint-limits* nil)


(defn compute-robot-info [#^NodeHandle nh]
  (when-not *robot-xml*
   (def *robot-xml* 
       (parse (java.io.ByteArrayInputStream. 
	       (.getBytes (.getStringParam nh "/robot_description") "UTF-8"))))
   (def *robot-joint-limits*
       (into {}
	 (for [joint (:content *robot-xml*)
	       :when (and (= (:tag joint) :joint)
			  (every? (or (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) {})
				  [:min :max]))]
	   [(:name (:attrs joint))
	    (vec (map read-string
		   (map (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) [:min :max])))])))
   (def *robot-safe-joint-limits*
       (into {}
	 (for [joint (:content *robot-xml*)
	       :when (and (= (:tag joint) :joint)
			  (every? (or (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) {})
				  [:min :max]))]
	   [(:name (:attrs joint))
	    (let [[min max]
	          (map read-string
		    (map (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) 
			 [:min :max]))
		  [smin smax] 
		  (map read-string
		    (map (:attrs (first (filter #(= (:tag %) :limit) (:content joint)))) 
			 [:safety_length_min :safety_length_max]))]
	      [(+ min smin) (- max smax)])])))
   ))

(defn get-robot-joint-limits [#^NodeHandle nh]
  (when-not *robot-joint-limits* (compute-robot-info nh))
  *robot-joint-limits*
  )

(defn get-robot-safe-joint-limits [#^NodeHandle nh]
  (when-not *robot-safe-joint-limits* (compute-robot-info nh))
  *robot-safe-joint-limits*
  )


(defn get-current-mechanism-state [#^NodeHandle nh]
  (get-message nh "/mechanism_state" (MechanismState.)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Load parts, define robot state objects ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmulti get-joint-map :class)

(def *missing-part* {:class ::MissingPart})
(defmethod get-joint-map ::MissingPart [p] {})

(load "robot/perception" "robot/base" "robot/arm" 
      "robot/torso" "robot/gripper" "robot/head")

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






(set! *warn-on-reflection* false)

