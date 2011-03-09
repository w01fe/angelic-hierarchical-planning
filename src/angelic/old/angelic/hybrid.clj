;; This file defines some additional shared utilities for hybrid angelic planning.

(ns angelic.old.angelic.hybrid
  (:use clojure.test angelic.old.angelic
	[angelic.old [ util :as util] [envs :as envs]]
	[angelic.util [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]
	[angelic.old.envs.hybrid-strips :as hs]
	[angelic.old.envs.hybrid-strips [constraints :as hc] [effects :as he]]))

;; The actions returned by hybrid planners should be quasi-primitive, plus a :num-var-map
;; key that maps each numeric variable to either a number, or an LP variable name.  
;; TODO: the latter more or less preculdes proper duplicate detection. solutions?

(def *hybrid-finish-description-schema* {:class ::HybridFinishDescriptionSchema})

(defn make-hybrid-finish-description [goal objects constant-fns]
  {:class ::HybridFinishDescription
   :goal goal 
   :objects objects
   :constant-fns constant-fns})

(defmethod instantiate-description-schema ::HybridFinishDescriptionSchema [desc instance]
  (make-hybrid-finish-description 
   (envs/get-goal instance) (util/safe-get instance :objects) (util/safe-get instance :constant-numeric-vals)))

(defmethod ground-description             ::HybridFinishDescription [desc var-map]  desc)

(defn make-hybrid-finish-valuation [rew extra-keys]
  (merge extra-keys 
         (map->valuation :angelic.old.angelic.dnf-valuations/DNFSimpleValuation 
                         {*finish-state* rew})))

;; TODO: fix
(defmethod progress-valuation    [:angelic.old.angelic/ConditionalValuation ::HybridFinishDescription] [val desc]
  (map->valuation :angelic.old.angelic.dnf-valuations/DNFSimpleValuation 
                  {*finish-state* (valuation-max-reward val)}))

