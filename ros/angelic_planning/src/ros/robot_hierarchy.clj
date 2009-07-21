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
   [ros.robot-actions :as ra]
   [edu.berkeley.ai [util :as util] [envs :as envs]] 
   [edu.berkeley.ai.envs.states :as states]
   [edu.berkeley.ai.angelic :as angelic]
   [edu.berkeley.ai.angelic.hierarchies :as hierarchies])
  )
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrapper for env defined in robot-env.
; Environment is just a robot-env 

; Punt on action space for now
(defn make-dummy-action-space []
  {:class ::DummyActionSpace})


(defn make-angelic-robot-env [robot-env goal-pred]
  (envs/make-environment
   robot-env
   (states/make-state-set str)
   (make-dummy-action-space)
   (envs/make-simple-condition goal-pred true)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
; Need optimistic descriptions for high-level actions ...

(defn make-angelic-robot-hierarchy [env]
;  ...
 )

(defmethod hierarchies/hla-primitive? ::ra/RobotAction [a]
  (ra/robot-action-primitive? a))

  

(defmethod hierarchies/hla-environment                        ::NavRegionsHLA [hla]
  (util/safe-get hla :env))

(defmethod hierarchies/hla-default-optimistic-valuation-type  ::NavRegionsHLA [hla]
  ::angelic/ExplicitValuation)

(defmethod hierarchies/hla-default-pessimistic-valuation-type ::NavRegionsHLA [hla]
  ::angelic/ExplicitValuation)


(defmethod hierarchies/hla-name ::NavRegionsAct       [hla] '[act])
(defmethod hierarchies/hla-name ::NavRegionsTraverse  [hla] ['traverse (:src hla) (:dst hla)])
(defmethod hierarchies/hla-name ::NavRegionsNav       [hla] ['nav (:dst hla)])
(defmethod hierarchies/hla-name ::NavRegionsPrimitive [hla] (:name (:primitive hla)))
(defmethod hierarchies/hla-name ::NavRegionsFinish    [hla] '[finish])

(defmethod hierarchies/hla-hierarchical-preconditions ::NavRegionsHLA [hla] 
  envs/*true-condition*)

; hierarchy : nav (square/connector)
;           : traverse (from in-connector to out-connector)

; initial-plan: either nav(dst) or nav(some conn), traverse(some final conn), nav(dst)

(defmethod hierarchies/hla-immediate-refinements 
  [::NavRegionsAct ::angelic/ExplicitValuation]            [hla opt-val]
  (let [cpos (util/safe-singleton (keys (angelic/explicit-valuation-map opt-val)))
	env  (:env hla)
	connect (util/safe-get-in hla [:primitives 'connect])
	{:keys [goal-pos region-fn region-connectors connector-dists connector-targets]} env]
    (concat
     (when (= (region-fn cpos) (region-fn goal-pos))
       [[(make-nav-hla hla goal-pos)]])
     (if (find connector-targets cpos)  ; already at connector
         (for [[connector rew] (connector-dists cpos)
	       :when (or (= (region-fn (connector-targets connector)) (region-fn goal-pos))
			 (seq (connector-dists (connector-targets connector))))]
	   [(make-traverse-hla hla cpos connector rew) connect hla])
       (for [connector (region-connectors (region-fn cpos))
	     :when (or (= (region-fn (connector-targets connector)) (region-fn goal-pos))
		       (seq (connector-dists (connector-targets connector))))]
	 [(make-nav-hla hla connector) connect hla])))))



(defmethod hierarchies/hla-optimistic-description             ::NavRegionsHLA [hla]
  (util/safe-get hla :optimistic-description))

(defmethod hierarchies/hla-pessimistic-description            ::NavRegionsHLA [hla]
  (util/safe-get hla :pessimistic-description))

