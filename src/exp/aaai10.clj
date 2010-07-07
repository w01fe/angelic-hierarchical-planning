(ns exp.aaai10
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [exp [env :as env] [hierarchy :as hierarchy] [hierarchical-incremental-search :as his]]
           [exp.2d-manipulation :as m2d]
	   [edu.berkeley.ai.util.experiments :as experiments]))

(def *exp-result* ::ExpResult)

(defstruct exp-result 
  :class :experiment :commit-id :timeout? :memout? :output :printed :init-ms :ms :mb
  :next-count :opt-count :pess-count :ref-count :plan-count)

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
  (env/reset-next-counter)
  (hierarchy/reset-ref-counter))

(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (struct exp-result ::ExpResult
          experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
          (util/sref-get env/*next-counter*)
          (util/sref-get env/*optimistic-counter*)
          (util/sref-get env/*pessimistic-counter*)
          (util/sref-get hierarchy/*ref-counter*)
          (util/sref-get hierarchy/*plan-counter*)))

;;;;;;; 2d-nav 

(defn make-exp-set []
  (experiments/make-experiment-set "prelim-2dnav"
    [:product
     [:objects [1 2 4 6 8 10]]
     [:rand    [1]]
     [:alg     (map first his/aaai-algs)]]
    (fn [m]
      `(m2d/make-2d-manipulation-hierarchy
        (m2d/make-random-2d-manipulation-env ~(:objects m) ~(:rand m))))
    (fn [m] `((get his/aaai-alg-map ~(:alg m)) ~'init))
    'exp.aaai10 nil 1000 512 false ::ExpResult))

; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

;;;;;; charts

(def *chart-folder* "/Users/jawolfe/Projects/reports/10aaai-btamp/poster/figs/")


