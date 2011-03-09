(ns angelic.old.envs.strips
 (:refer-clojure) 
 (:import [java.util HashMap HashSet Arrays ArrayList])
 (:require [angelic.util.propositions :as props]
           [angelic.util :as util] [angelic.old  [envs :as envs]]
           [angelic.old.envs.states.binary :as binary-states]
	   [angelic.old.envs.strips.smart-csps :as smart-csps]))

(load "strips/domains")
(load "strips/instances")


