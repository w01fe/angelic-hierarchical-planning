(ns angelic.scripts.experiments-11aaai
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.search.textbook :as textbook]
           [angelic.domains.discrete-manipulation :as dm]
           [angelic.search.implicit
            [ah-astar :as aha]
            [sahtn :as sahtn]
            [dash-astar-opt :as dao]]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
          (util/sref-get hierarchy/*optimistic-counter*)
          (util/sref-get hierarchy/*pessimistic-counter*)
          (util/sref-get hierarchy/*ref-counter*)
          (util/sref-get hierarchy/*plan-counter*)))

;;;;;;;;;;;;;;;;;; Discrete manipulation experiments ;;;;;;;;;;;;;;;;;;;;;

(def alg-forms
     {:sahtn   (fn [m] `(sahtn/sahtn ~'init #{:nav :reach :discretem-tla}))
      :aha*    (fn [m] `(aha/ah-a* ~'init true))
      :dash-a* (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                                  :choice-fn rand-nth))})

(defn make-dm-exp-set []
  (experiments/make-experiment-set "11aaai-dm"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:rand    [1 2 3]]
     [:alg     (keys alg-forms)]]
    (fn [m]
      `(dm/make-discrete-manipulation-hierarchy
        (dm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m))))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.experiments-11aaai 10 3600 512 false ::ExpResult))

(defonce *dm-results* nil)
(defn read-results []
  (def *dm-results* 
       (experiments/experiment-set-results->dataset 
        (experiments/read-experiment-set-results (make-dm-exp-set)))))



;(use '[edu.berkeley.ai.util experiments cluster] 'angelic.scripts.experiments-11aaai)
;(run-experiment-set-cluster (make-dm-exp-set))

; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

