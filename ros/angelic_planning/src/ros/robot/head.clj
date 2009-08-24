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

(defn point-head [#^NodeHandle nh point-stamped] 
  (put-single-message-cached nh "/head_controller/point_head" 
    (map-msg PointStamped point-stamped)))

(defn look-at [nh base-link-xyz]
  (point-head nh {:header {:frame_id "/base_link"}
		  :point  (make-point base-link-xyz)}))

(defonce *head-point-stamped* (atom nil))

(defn track-head
  "Start the head tracking a particular point-stamped, or switch tracking to a new point-stamped.
   Pass nil to stop head tracking."
  ([nh] (track-head nh {:header {:frame_id "/base_link"} :point (make-point [1 0 1])}))
  ([nh point-stamped]
     (let [start? (and point-stamped (not @*head-point-stamped*))]
       (reset! *head-point-stamped* point-stamped)
       (when start?
	 (.run 
	  (Thread. 
	   (proxy [Runnable] []
	    (run [] 
	     (loop []
	       (when-let [pt @*head-point-stamped*]
		 (point-head nh pt)
		 (Thread/sleep 100)
		 (recur)))))))))))


       
       