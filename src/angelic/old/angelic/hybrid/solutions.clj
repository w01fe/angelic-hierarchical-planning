;; This file defines valuations for hybrid problems, where the discrete part of the state
;; is always known but we may be angelic about the continuous part.  

;; In particular, a hybrid-fixed-lp-valuation consists of a set of true discrete propositions,
;; together with a continuous-lp-state for the continuous variables.  

;; A corresponding kind of description, corresponding to a primitive, discrete-grounded
;; but continuous-ungrounded hybrid strips action, is also defined.

(ns angelic.old.angelic.hybrid.solutions
  (:use clojure.test angelic.old.angelic
	[angelic.old [ util :as util] [envs :as envs]]
	[angelic.util [hybrid :as hybrid] [lp :as lp] [linear-expressions :as le]]
	[angelic.old.envs.hybrid-strips :as hs]
	[angelic.old.envs.hybrid-strips [constraints :as hc] [effects :as he]]
	[angelic.old.angelic.hybrid [continuous-lp-states :as cls] [fixed-lp-valuations :as hflv]]))




(defn extract-hybrid-primitive-solution 
  "Take a solution (quasi-ground) primitive sequence and the final
   outcome, a hybrid-fixed-LP-valuation, and return a fully grounded
   sequence of hybrid-strips actions that achieves the optimal reward."
  [env act-seq]
  (let [action-space (:action-space env)
	objects      (util/safe-get env :objects)
	const-fns    (util/safe-get env :constant-numeric-vals)
	final-val    (reduce (fn [val act]
			       (progress-valuation val
                                 (make-quasiground-primitive-description 
                                  act objects const-fns (util/safe-get act :num-var-map))))
			     (map->valuation ::hflv/HybridFixedLPValuation {(envs/get-initial-state env) 0})
			     act-seq)
	[cont-result num-var-map rew] (util/first-maximal-element #(nth % 2)
				        (util/map-when #(cls/solve-lp-state %) 
                                             (util/safe-get final-val :continuous-lp-states)))]
    (map #(hs/hybrid-strips-action->action (:schema  %)
	    (into (util/safe-get % :var-map) 
                  (for [nv (util/safe-get % :num-vars)] 
                    [nv (util/safe-get num-var-map (util/safe-get (:num-var-map %) nv))]))
            action-space) act-seq)))

