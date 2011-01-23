(ns angelic.scripts.experiments-11ijcai
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.domains.sas-problems :as sas-problems]
           [angelic.domains.taxi-constrained :as taxi]           
           [angelic.search.textbook :as textbook]
           [angelic.search.action-set.asplan :as asplan]
           [angelic.search.action-set.stratified :as strat]
	   [edu.berkeley.ai.util.experiments :as experiments]))

(def *exp-result* ::ExpResult)

(defstruct exp-result 
  :class :experiment :commit-id :timeout? :memout? :output :printed :init-ms :ms :mb
  :next-count :add-count)

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
           (env/reset-next-counter)
           (util/sref-set! asplan/*add-count* 0))


(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (struct exp-result ::ExpResult
          experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
          (util/sref-get env/*next-counter*)
          (util/sref-get asplan/*add-count*)
          ))


;;;;; Taxi

(def taxi-algs
  {:strat "strat"
   :strat+ "strat+"})

(def taxi-types
     {:independent ["independent" "individual taxis"]
      :pairwise ["pairwise" "pairwise taxis"]
      :single ["single" "single taxi"]})

(def taxi-factories
     {:independent taxi/make-random-independent-taxi-env
      :pairwise taxi/make-random-pairwise-taxi-env
      :single taxi/make-random-single-taxi-env })

(defn make-taxi-exp-set []
   (experiments/make-experiment-set
    "ib-taxi-strat"
    [:product
     [:size (vec (range 1 11))]
     [:constrain? [true]]
     [:alg (keys taxi-algs)]
     [:type (keys taxi-types)]]    
    (fn [m]
      `((taxi-factories ~(:type m)) 3 3 ~(:size m) ~(:constrain? m) ~(if (= (:type m) :single) 6 1)))
    (fn [m] `(strat/stratified-search ~'init ~(if (= (:alg m) :strat) :simple :fluid)))
    'angelic.scripts.experiments-11icaps 10 3600 512 false ::ExpResult))

;(use '[edu.berkeley.ai.util experiments cluster] 'angelic.scripts.experiments-11ijcai)
;(run-experiment-set-cluster (make-exp-set))
