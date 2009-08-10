(in-ns 'user)


(go-arm "grasp_bar_low")

; sink
(go-base "sink")
(servo-to-sink nh)
(move-arm-to-pos nh [0.7 0 1.0] true 30)
(move-arm-directly-to-state nh (update-in (get-current-arm-state nh true) [:joint-angle-map "r_wrist_roll_joint"] + Math/PI))
; x2
(homes)

(do-throw nh "_new")

; trash
(go-base "trash")
(servo-to-trash nh)
(go-arm-traj *drop-traj2*)
(open)
(home)

; Counter - 43 in.