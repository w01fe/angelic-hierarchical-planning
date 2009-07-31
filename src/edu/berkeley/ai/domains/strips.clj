(ns edu.berkeley.ai.domains.strips
 (:refer-clojure) 
 (:import [java.util HashMap HashSet Arrays ArrayList])
 (:require [edu.berkeley.ai.util.propositions :as props]
           [edu.berkeley.ai [util :as util] [envs :as envs]]
           [edu.berkeley.ai.envs.states.binary :as binary-states]
	   [edu.berkeley.ai.domains.strips.smart-csps :as smart-csps]))

(load "strips/domains")
(load "strips/instances")


