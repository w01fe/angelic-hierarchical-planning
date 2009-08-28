(in-ns 'user)

(open)
(close)
(close-gripper nh 45 true)

(grasp-rviz nh)
(grasp-nearest nh 0.75)

(home)
(homeu)

; Trajectories
(go-arm-traj *serve-high*)
(go-arm-traj *serve-low*)

; Spinning
(go-arm-plan "grasp_counter")
(go-arm-plan "grasp_bar_low")

; With constraitns
(go-arm-plan "grasp_counter" true)
(go-arm-plan "grasp_bar_low" true)

 
; sink
(go-base "sink")
(laser-slow)
(servo-to-sink nh)
(move-arm-to-pos nh [0.7 0 1.0] true 30)
(move-arm-directly-to-state nh (update-in (get-current-arm-state nh true) [:joint-angle-map "r_wrist_roll_joint"] + Math/PI))
; x2
(homes)
(laser-fast)

(do-throw nh "_new")

; trash
(go-base "trash")
(servo-to-trash nh)
(go-arm-traj *drop-traj2*)
(open)
(home)
a
; Counter - 43 in.

(move-gripper-rel nh [0 0 0.1] true)

(shake-drink nh)

(look-around nh) 
(look-forward nh)

(go-base "bar3")
(servo-to-bar nh)

(grasp-rviz nh)

(grasp-nearest nh)


(look-l nh)
(look-dl nh)

(look-lf nh)
(look-dlf nh)

(look-f nh)
(look-df nh)

(look-rf nh)
(look-drf nh)

(look-r nh)
(look-dr nh)