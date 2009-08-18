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

(defmsgs [geometry_msgs PointStamped])
;(defsrvs [motion_planning_msgs FindBottles])

(defn laser-slow [] (util/sh "roslaunch" "/u/jawolfe/angel/ros/angelic_planning/launch/laser_slow.launch"))
(defn laser-fast [] (util/sh "roslaunch" "/u/jawolfe/angel/ros/angelic_planning/launch/laser_fast.launch"))
  

(def *rviz-point-map* (atom nil))
(def *rviz-point-base* (atom nil))

(defn setup-rviz-points [#^NodeHandle nh]
  (println "Starting point collection...")
  (.subscribe nh "/selected_point" (PointStamped.)
	     (sub-cb [m]
	       (println "Got new rviz point!")
	       (assert (= (:frame_id (:header m)) "/map"))
	       (reset! *rviz-point-map* (decode-point (:point m)))
	       (reset! *rviz-point-base* (transform-point-tf nh "/map" "/base_link" (decode-point (:point m)))))
	     1))

(let [mem (atom {})]
  (def get-rviz-points
     (fn [#^NodeHandle nh wait?]
       (future-call laser-slow)
       (when-not (@mem nh) 
	 (do
	   (setup-rviz-points nh)
	   (swap! mem assoc nh true)))
       (when wait? (reset! *rviz-point-map* nil))
       (.spinOnce nh)
       (when wait?
	 (while (not @*rviz-point-map*)
	   (.spinOnce nh)))
       (future-call laser-fast)
       (when @*rviz-point-map*
	 [@*rviz-point-map* @*rviz-point-base*]))))



(comment

(defn find-bottles [nh z]
  (:pts (call-srv nh "/find_bottles" (map-msg FindBottles$Request {:z z}))))

(defn wait-for-bottle [nh z]
  (laser-slow)
;  (Thread/sleep 2000)
  (loop [bottles (find-bottles nh z)]
    (if (empty? bottles)
        (do (print ".")
	    (Thread/sleep 100)
	    (recur (find-bottles nh z)))
      (do (future-call laser-fast)
	  (let [bottles (map #(decode-point (:point %)) bottles)]
	    (println "Got bottles" bottles)
	    (update-in 
	     (util/first-maximal-element 
	      #(- 100 (Math/abs (double (second %))))
	      bottles)
	     [2] - 0.02)
	    )))))

(defn get-trash-point [nh]
  (let [p (get-single-message-cached nh "/trash_can" (PointStamped.))]
    (transform-point nh (:frame_id (:header p)) "/base_link" (decode-point (:point p)))))

 )