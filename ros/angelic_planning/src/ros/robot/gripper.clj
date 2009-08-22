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
  
(defmsgs  [std_msgs          Float64]
          [move_arm          ActuateGripperAction]
	  [mapping_msgs      AttachedObject Object]
	  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Gripper States, getters ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::LeftGripperState ::GripperState)
(derive ::LeftGripperState ::Left)
(derive ::RightGripperState ::GripperState)
(derive ::RightGripperState ::Right)

(defstruct robot-gripper-state :class :open? :force :holding)

(defn make-robot-gripper-state 
  "What it sounds like.  Holding should eventually describe the object geometry; 
   for now, it's treated as a boolean: holding an odwalla bottle or not."
  ([right? open?]
     (make-robot-gripper-state right? open? (if open? 100 60) false))
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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Attaching objects ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO:  make generic.


(defn attach-bottle [#^NodeHandle nh]
  (println "Not attaching objects for now.")
#_  (put-single-message-cached nh "/attach_object" 
    (map-msg AttachedObject
     {:header {:frame_id "r_gripper_palm_link" :stamp (.now nh)}
      :link_name "r_gripper_palm_link"
      :objects [{:type ros.pkg.mapping_msgs.msg.Object/CYLINDER
		 :dimensions [0.075 0.30]
		 :triangles []
		 :vertices []}]
      :poses   [(make-pose [0.16 0 0] [0 0 0 1])]
      :touch_links ??
      }) 
    ))

(defn unattach-bottle [nh]
  (put-single-message-cached nh "/attach_object"
    (map-msg AttachedObject
     {:header {:frame_id "r_gripper_palm_link"}
      :link_name "r_gripper_palm_link"
      :objects []
      :poses []
      :touch_links []
      }) 
    ))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Actuating gripper  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn apply-gripper-force [#^NodeHandle nh right? force]
  (start-action-async nh (str "/actuate_gripper_" (if right? "right" "left") "_arm")
	      ActuateGripperAction {:data force} true))

; Running synchronously results in long lag times...
;  (run-action nh (str "/actuate_gripper_" (if right? "right" "left") "_arm")
;	      ActuateGripperAction {:data force}))

(defn move-gripper-to-state 
  ([nh gs]
    (apply-gripper-force nh (isa? (:class gs) ::Right) (* (:force gs) (if (:open? gs) 1 -1)))
    (if (:holding gs) (attach-bottle nh) (unattach-bottle nh))))


(defn open-gripper [nh right?]
  (apply-gripper-force nh right? 100)
  )

(defn close-gripper 
  ([nh right?] (close-gripper nh right? 60 false))
  ([nh right? force empty?] 
     (apply-gripper-force nh right? (- force))
     ))







