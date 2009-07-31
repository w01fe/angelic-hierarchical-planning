(ns edu.berkeley.ai.domains.strips
 (:refer-clojure)
 (:require [edu.berkeley.ai.util.propositions :as props]
           [edu.berkeley.ai [util :as util] [envs :as envs]]
           [edu.berkeley.ai.envs.states.binary :as binary-states]
       [edu.berkeley.ai.search.smart-csps :as smart-csps]))

(load-file "strips/domains.clj")
(load-file "strips/instances.clj")


