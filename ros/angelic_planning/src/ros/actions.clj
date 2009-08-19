;///////////////////////////////////////////////////////////////////////////////
;// A Clojure action client for rosjava
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

;;; Clojure implementation of *old* action client 
; (and partially completed action server)


(ns ros.actions
  (:use ros.ros))   


(set! *warn-on-reflection* true)

(import-ros)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                       New Action (actionlib) Client
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmsgs [actionlib GoalStatus GoalID])

(def *action-statuses*
 [[:pending    (GoalStatus/PENDING)]
  [:active     (GoalStatus/ACTIVE)]
  [:preempted  (GoalStatus/PREEMPTED)]
  [:succeeded  (GoalStatus/SUCCEEDED)]
  [:aborted    (GoalStatus/ABORTED)]
  [:rejected   (GoalStatus/REJECTED)]
  [:preempting (GoalStatus/PREEMPTING)]
  [:recalling  (GoalStatus/RECALLING)]
  [:recalled   (GoalStatus/RECALLED)]])

(def *action-status-forward* (into {} *action-statuses*))
(def *action-status-backward* (into {} (map (fn [[x y]] [(int y) x]) *action-statuses*)))
(def *terminal-action-statuses* #{:preempted :succeeded :aborted :rejected :recalled}) 

(defn action-status [code] (safe-get* *action-status-backward* (int code)))
(defn action-status-code [status] (safe-get* *action-status-forward* status))

(defn- action-goal-msg [action-class]
  (.newInstance #^Class (:class (:action_goal (msg-map (.newInstance #^Class action-class))))))

(defn- action-result-msg [action-class]
  (.newInstance #^Class (:class (:action_result (msg-map (.newInstance #^Class action-class))))))

(defn- action-feedback-msg [action-class]
  (.newInstance #^Class (:class (:action_feedback (msg-map (.newInstance #^Class action-class))))))




(defn make-action-client 
  "Create a persistent, simple action client with the provided name and message types."
  [#^NodeHandle nh name action-class]
  (let [result-cb  (Subscriber$QueueingCallback.)
	result-sub   (.subscribe nh (str name "/result") (action-result-msg action-class) result-cb 1)
	goal-pub     (.advertise nh (str name "/goal")   (action-goal-msg action-class) 1)
        cancel-pub   (.advertise nh (str name "/cancel") (GoalID.) 1)
	start-time (.now nh)]
    (loop []
      (Thread/sleep 1)
      (if (and (< (.getNumSubscribers goal-pub) 1) (< (.getNumSubscribers cancel-pub) 1))
  	  (if (.hasElapsed start-time (Duration. 1.0))
	      (do (println "Action client did not recieve subscribers"
			   (.getNumSubscribers goal-pub) (.getNumSubscribers cancel-pub))
		  (.logError nh "Action client did not recieve subscribers")
		  (.shutdown result-sub) (.shutdown goal-pub) (.shutdown cancel-pub)
		  nil)
	    (recur))
	{:node-handle nh
	 :action      action-class
	 :result-sub  result-sub
	 :result-cb   result-cb
	 :goal-pub    goal-pub
	 :cancel-pub  cancel-pub}))))

(defn cancel-action-client 
  "Preempt a currently executing action client"
  [ac goal-id]
  (.publish #^Publisher (:cancel-pub ac) (map-msg goal-id)))

(defn- equal-goals? [#^Time g1 #^Time g2]
  (and (= (.secs g1) (.secs g2)) (= (.nsecs g1) (.nsecs g2)))) 

(defn execute-action-client 
  "Actually execute an existing action client, waiting at most Duration
   for it to succeed.  Returns the final status."
  ([ac goal-msg] (execute-action-client ac goal-msg Duration/MAX_VALUE))
  ([ac goal-msg #^Duration duration]
     (let [#^NodeHandle nh (:node-handle ac)
	   start-time (.now nh)
	   goal-id    {:class GoalID :stamp start-time :id start-time}
	   result-q   #^Subscriber$QueueingCallback (:result-cb ac)]
       (.clear result-q)
       (.publish #^Publisher (:goal-pub ac)
	 (map-msg {:class (:class (:action_goal (msg-map (.newInstance #^Class (:action ac)))))
		   :header {:frame_id "/map"}
		   :goal_id goal-id
		   :goal goal-msg}))
       (while (and (not (.hasElapsed start-time duration))
		   (or (.isEmpty result-q)
		       (and (not (equal-goals? start-time (:id (:goal_id (:status (msg-map (.peek result-q)))))))
			    (do (.pop result-q) true))))
		       
	 (.spinOnce nh))
       (if (.hasElapsed start-time duration)
	   (do (println "preempting!")
	       (cancel-action-client ac goal-id)
	       :preempting)
         (let [result      (msg-map (.pop result-q))
	       goal-status (:status result)
	       status-goal-id #^Time (:id (:goal_id goal-status))
	       status      (*action-status-backward* (int (:status goal-status)))]
	   (assert (and (= (.secs status-goal-id) (.secs start-time)) (= (.nsecs status-goal-id) (.nsecs start-time))))
;	   (println "Action finished with status" status "and text" (:text goal-status))
	   [status (:result result)])))))


(defn shutdown-action-client 
  "Destroy this persistent action client.  Does not preempt any running actions."
  [ac]
  (.shutdown #^Subscriber (:result-sub ac))
  (.shutdown #^Publisher  (:goal-pub     ac))
  (.shutdown #^Publisher  (:cancel-pub  ac)))


(defn run-action
  "Create, execute, and then destroy an action client."
  ([nh name action goal-msg] 
     (run-action nh name action goal-msg Duration/MAX_VALUE))
  ([nh name action goal-msg duration]
     (when-let [ac (make-action-client nh name action)]
       (let [result (execute-action-client ac goal-msg duration)]
	 (shutdown-action-client ac)
	  result))))

(defn cancel-action-async
  "Cancel all goals associated with a given action."
  [nh name]
  (put-single-message nh (str name "/cancel")
    (map-msg {:class GoalID
	      :stamp (Time.)
	      :id    (Time.)}) 1))

(defn start-action-async
  "Start an action running by firing off a goal message.  No
   further interaction with the action is possible."
  ([nh name action goal-msg] (start-action-async nh name action goal-msg false))
  ([nh name action goal-msg cancel-others?]
    (when cancel-others? (cancel-action-async nh name))
    (put-single-message nh (str name "/goal") 
      (map-msg {:class (:class (:action_goal (msg-map (.newInstance #^Class action))))
	        :header {:frame_id "/map"}
	        :goal_id {:stamp (Time.) :id (Time.)}
	        :goal goal-msg})
      1)))

 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                             Old Action Client
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defmsgs [std_msgs Empty]
	 [robot_actions ActionStatus])

(def *old-action-statuses*
     [[:reset (ActionStatus/RESET)]
      [:success   (ActionStatus/SUCCESS)]
      [:aborted   (ActionStatus/ABORTED)]
      [:preempted (ActionStatus/PREEMPTED)]
      [:active    (ActionStatus/ACTIVE)]])

(def *old-action-status-forward* (into {} *old-action-statuses*))
(def *old-action-status-backward* (into {} (map (fn [[x y]] [(int y) x]) *old-action-statuses*)))
 
(defn old-action-status [code] (safe-get* *old-action-status-backward* (int code)))
(defn old-action-status-code [status] (safe-get* *old-action-status-forward* status))



(defn make-old-action-client 
  "Create a persistent action client with the provided name and message types."
  [#^NodeHandle nh name goal-msg state-msg]
  (let [feedback-cb  (Subscriber$QueueingCallback.)
	feedback-sub (.subscribe nh (str name "/feedback") state-msg feedback-cb 1)
	goal-pub     (.advertise nh (str name "/activate") goal-msg 1)
        preempt-pub  (.advertise nh (str name "/preempt")  (Empty.) 1)
	start-time (.now nh)]
    (loop []
      (Thread/sleep 1)
      (if (and (< (.getNumSubscribers goal-pub) 1) (< (.getNumSubscribers preempt-pub) 1))
  	  (if (.hasElapsed start-time (Duration. 10.0))
	      (do (println "Action client did not recieve subscribers"
			   (.getNumSubscribers goal-pub) (.getNumSubscribers preempt-pub))
		  (.logError nh "Action client did not recieve subscribers")
		  (.shutdown feedback-sub) (.shutdown goal-pub) (.shutdown preempt-pub)
		  nil)
	    (recur))
	{:node-handle  nh
	 :goal-class   (class goal-msg)
	 :feedback-sub feedback-sub
	 :feedback-cb  feedback-cb
	 :feedback     (atom nil)
	 :status       (atom :reset)
	 :goal-pub     goal-pub
	 :preempt-pub  preempt-pub}))))

(defn- process-status-callback [ac]
  (. #^NodeHandle (:node-handle ac) spinOnce)
  (let [#^Subscriber$QueueingCallback cb (:feedback-cb ac)]
    (when-not (.isEmpty cb)
      (let [m (msg-map (.pop cb))]
	(reset! (:feedback ac) (safe-get* m :feedback))
	(reset! (:status   ac) (old-action-status (:value (:status m))))))))

(defn preempt-old-action-client 
  "Preempt a currently executing action client"
  [ac]
  (.publish #^Publisher (:preempt-pub ac) (Empty.)))


(defn execute-old-action-client 
  "Actually execute an existing action client, waiting at most Duration
   for it to succeed.  Returns the final status."
  ([ac goal-msg] (execute-old-action-client ac goal-msg Duration/MAX_VALUE))
  ([ac goal-msg #^Duration duration]
     (let [#^NodeHandle nh (:node-handle ac)
	   start-time (.now nh)]
       (reset! (:status ac) :reset)
       (.clear #^Subscriber$QueueingCallback (:feedback-cb ac))
       (.publish #^Publisher (:goal-pub ac) goal-msg)
       (while (and (not (.hasElapsed start-time duration)) 
		   (not (= :active @(:status ac))))
	 (Thread/sleep 1)
	 (process-status-callback ac))
       (if (.hasElapsed start-time duration)
	   (do (println "preempting before starting!")
	       (reset! (:status ac) :preempted)
	       (preempt-old-action-client ac))
	 (while (= :active @(:status ac))
	   (Thread/sleep 1)
	   (process-status-callback ac)
	   (when (.hasElapsed start-time duration) (println "preempting while running!") (preempt-old-action-client ac))))
       @(:status ac))))


(defn old-action-client-feedback 
  "Get the last feedback message received by this action client."
  [ac]
  @(:feedback ac))
  

(defn shutdown-old-action-client 
  "Destroy this persistent action client and preempt the action's execution."
  [ac]
  (preempt-old-action-client ac)
  (.shutdown #^Subscriber (:feedback-sub ac))
  (.shutdown #^Publisher  (:goal-pub     ac))
  (.shutdown #^Publisher  (:preempt-pub  ac)))


(defn run-old-action
  "Create, execute, and then destroy an action client."
  ([nh name goal-msg empty-state-msg] 
     (run-old-action nh name goal-msg empty-state-msg Duration/MAX_VALUE))
  ([nh name goal-msg empty-state-msg duration]
     (let [ac (make-old-action-client nh name goal-msg empty-state-msg)
	   result (execute-old-action-client ac goal-msg duration)]
       (shutdown-old-action-client ac)
       result)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                        Action Server (in progress)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   
     



(comment 
(defn- action-server-runner [#^NodeHandle nh name goal-msg state-msg exec-fn status]
 (let [state        (atom (msg-map state-msg))
       action       (atom nil)
       feedback-pub (.advertise nh (str name "/feedback") state-msg 1)
       goal-cb      (Subscriber$QueueingCallback.)
       goal-sub     (.subscribe nh (str name "/activate") goal-msg goal-cb 1)
       preempt-cb   (Subscriber$QueueingCallback.)
       preempt-sub  (.subscribe nh (str name "/preempt") (Empty.) preempt-cb 1)]
   (while (not (= @status :aborted))
     
     ...)
   (when @action
     (preempt)
     (wait)
     (send out aborted message))
   (.shutdown feedback-pub) (.shutdown goal-sub) (.shutdown preempt-su b)))

;				 (sub-cb [] 
;				   (if-let [[#^ExecutorService pool #^Future f] (@runner)]
;				       (do (.cancel f true)
;					   (.shutdownNow pool)
;					   (when-not (.awaitTermination pool 10 java.util.concurrent.TimeUnit/SECONDS)
;					     (println "shutdown failed"))
;					   (reset! runner nil))
;				     (println "Not currently running!"))))

;					 1)
;	start-time (.now nh)]  



(defn make-action-server [#^NodeHandle nh name goal-msg state-msg exec-fn]
  "Exec-fn takes a goal and feedback-pub-fn [feedback status] as arguments.
   It should expect to be interrupted on preemption."  
  (let [status (atom :reset)]
    [status (doto (Thread. #(action-server-runner nh name goal-msg state-msg exec-fn status)) (.start))]))

(defn shutdown-action-server [[serv-atom thread]]
  (reset! serv :aborted)
  (.join thread))

  )


	   


(set! *warn-on-reflection* false)