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
(defsrvs [find_bottles FindBottles] [tabletop_srvs FindTable])

(def *laser-state* (atom nil))

(defn laser-slow []
  (if (= @*laser-state* :slow) 
      (println "Laser should already be slow...")
    (do (util/sh "roslaunch" "/u/jawolfe/angel/ros/angelic_planning/launch/laser_slow.launch")
	(reset! *laser-state* :slow)
	(println "Laser is now slow."))))

(defn laser-fast [] 
  (if (= @*laser-state* :fast) 
      (println "Laser should already be fast...")
    (do (util/sh "roslaunch" "/u/jawolfe/angel/ros/angelic_planning/launch/laser_fast.launch")
	(reset! *laser-state* :fast)
	(println "Laser is now fast."))))

  

(def *rviz-point-map* (atom nil))
(def *rviz-point-base* (atom nil))

;; This assumes a hacked version of rviz that publishes selected points on the /selected_point topic...
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
 ;      (future-call laser-fast)
       (when @*rviz-point-map*
	 [@*rviz-point-map* @*rviz-point-base*]))))



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
      (do ;(future-call laser-fast)
	  (let [bottles (map #(decode-point (:point %)) bottles)]
	    (println "Got bottles" bottles)
	    (update-in 
	     (util/first-maximal-element 
	      #(- 100 (Math/abs (double (second %))))
	      bottles)
	     [2] - 0.02)
	    )))))


(defn find-table-objects [nh]
  (laser-slow)
  (:table (call-srv nh "/table_object_detector" (map-msg FindTable$Request {}))))

(defn wait-for-table-objects [nh]
;  (Thread/sleep 2000)
  (loop [table (find-table-objects nh)]
    (if (empty? (:objects table))
        (do (print ".")
	    (Thread/sleep 100)
	    (recur (find-table-objects nh)))
      table)))

(defn extract-center-table-object [table]
  (assert (seq (:objects table)))
  (assert (= (:frame_id (:header table)) "/base_link")) 
  (let [bottles (map (fn [obj] (map #(decode-point (% obj)) [:min_bound :center :max_bound])) 
		     (:objects table))]
    (println "Got bottles" bottles)  
    (util/first-maximal-element 
     #(- 100 (Math/abs (double (second (second %)))))
     bottles)
    ))



(defn find-object-rviz [nh]
  "Get the position of an object by waiting for the user to click on a point in rviz"
  (second (get-rviz-points nh true)))

(defn find-object-bottle [nh z]
  "Get the position of an object by using find_bottles"
  (wait-for-bottle nh z))

(defn find-object-table [nh]
  "Get the position of an object by using the table-object-detector"
  (let [[[minx miny minz] [cx cy cz] [maxx maxy maxz]]
	(extract-center-table-object (wait-for-table-objects nh))]
    [(+ minx 0.01) cy cz]))

(defn find-specific-object [nh map-pt max-dist]
  "Get the exact position of object in base-link, given an approximate map location."
  (let [table   (util/make-safe (wait-for-table-objects nh))
	[x y z] (transform-point-tf nh "/map" "/base_link" map-pt) 
	bottles (map (fn [obj] (map #(decode-point (% obj)) [:min_bound :center :max_bound])) 
		     (:objects table))
	[[minx miny minz] [cx cy cz] [maxx maxy maxz] :as best] 
	 (util/first-maximal-element 
	  (fn [[min [cx cy] max]]
	    (- 0 (Math/pow (double (- cx x)) 2) (Math/pow (double (- cy y)) 2)))
	  bottles)
	dist (Math/sqrt (+ (Math/pow (double (- cx x)) 2) (Math/pow (double (- cy y)) 2)))]
    (assert (= (:frame_id (:header table)) "/base_link")) 
    (println "Got best bottle" best "with distance to given point" dist) 
    (assert (< dist max-dist))
    (assert (< minz z maxz))
    [(+ minx 0.01) cy cz]))

  


; Right now, nothing sets laser to fast...
; Height of table in green room is 0.75.

(comment


(defn get-trash-point [nh]
  (let [p (get-single-message-cached nh "/trash_can" (PointStamped.))]
    (transform-point nh (:frame_id (:header p)) "/base_link" (decode-point (:point p)))))

 )