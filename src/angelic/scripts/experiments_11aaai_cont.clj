(ns angelic.scripts.experiments-11aaai-cont
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [ros.planning.actions :as cm]
           [angelic.search.implicit
            [ah-astar :as aha]
            [sahtn :as sahtn]
            [dash-astar-opt :as dao]]))


;;;;;;;;;;;;;;;;;; Helpers - parsing LAMA output ;;;;;;;;;;;;;;;;;;;;;;;;;

(def alg-forms
     {:sahtn   (fn [m] `(sahtn/sahtn ~'init #{:nav :reach :discretem-tla '~'top '~'navh '~'navv}))
      :aha*    (fn [m] `(aha/ah-a* ~'init true))
      :dash-a* (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                                  :choice-fn rand-nth))})

(defn median-of [n items]
  (assert (odd? n))
  (let [ind (quot n 2)]
    (when (> (count items) ind)    
      (nth (sort items) ind))))

(defn solution-lengths [ds k nper]
  (util/map-vals (fn [es] (median-of nper (map #(count (first (:output %))) es)))
                 (group-by k
                  (filter #(and (= (:alg %) :dash-a*) (:ms %)) ds))))

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

(defmacro defresults [name es-maker]
  (let [sn (util/symbol-cat '* name '-results*)]
    `(do (defonce ~sn nil)
         (defn ~(util/symbol-cat 'read- name '-results) []
           (def ~sn
                (experiments/experiment-set-results->dataset
                 (experiments/read-experiment-set-results (~es-maker))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;; Continuous manipulation experiments ;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-cm-exp-set []
  (experiments/make-experiment-set "11aaai-cm"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:alg     (keys alg-forms)]
     [:rand    [0]]]
    (fn [m]
      `(cm/make-discrete-manipulation-hierarchy
        (cm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m))))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.experiments-11aaai-cont nil 3600 512 false ::ExpResult))


(defresults cm make-cm-exp-set)
(defresults dm-lama make-dm-lama-exp-set)


(defn read-all-results [] (read-dm-results) (read-dm-lama-results))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Discrete charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment


  (defn make-dm-charts 
    ([] (make-dm-charts "/Users/jawolfe/Projects/reports/11-aaai/graphs/"))
    ([dir]
       (doseq [[n ylabel field] [["evals" "\\# of evaluations" :opt-count]
                                 ["time"  "runtime (s)" :secs]]]
         (-> (datasets/ds-summarize
              (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms *dm-results*) :secs)
              [:objects :alg] [[field (fn [& args] (median-of 5 args)) #_util/mean field]])
             (datasets/ds->chart
              [:alg] :objects field
              {:term "solid dashed size 2.0,1.5"
               :ylog  "t" :xrange "[1:5]" ;             :yrange "[4:600]"
               :title "discrete pick-and-place problems" :key "bottom right" #_"at 2.6, 445"
               :xlabel "\\# of objects"
               :extra-commands [(str "set ylabel \"" ylabel "\" -2,0") "set xtics 1"]}            
              (let [c (util/counter-from 0)] (fn [& args] (let [v ([1 2 3 6] (c))]  {:lw 3 :pt v :lt v})))
              identity #_{[:ucs] "UCS" [:htn-ucs]  "H-UCS" [:sahtn] "SAHTN" [:nsahtn] "N-SAHTN"}
              identity #_(fn [l] (sort-by #(if (=  "UCS" (:title %)) "Q" (:title  %)) l)))
             (charts/plot)))))

  (defn parsed-lama []
    (for [e *dm-lama-results*]
      (let [m (parse-lama-output (:output e))]
        (assoc e :ms (* 1000 (:last-total-seconds m)) :opt-count (:generated m)))))


  (defn inst-name [m] (str (:objects m) "-" (:rand m)))
  (defn dm-result-map [ds]
    (util/map-vals
     (fn [exps]
       (util/map-vals (fn [es] (assert (= (count es) 1)) ((juxt :secs :opt-count) (first es)))
                      (group-by :objects #_ inst-name exps)))
     (group-by :alg
               #_ (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)            
               (datasets/ds-summarize
                (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)
                [:objects :alg] [[:secs #(median-of 5 %&) :secs] [:opt-count #(median-of 5 %&) :opt-count]]))))





  (defn pad-right [x n]  
    (let [xs (str x) 
          s #^String (str "                               " xs)]
      (assert (<= (.length xs) n))
      (.substring s (- (.length s) n))))

  (defn format-n [n dec]
    (let [base (util/expt 10 dec)]
      (/ (int (* base n)) (if (> dec 0) (double base) 1))))

  (defn make-dm-table []
    (let [res (merge (dm-result-map *dm-results*) (dm-result-map (parsed-lama)))
          lens (solution-lengths *dm-results* :objects 5)
          algs [:lama :sahtn :aha* :dash-a*]]
      (print "num & len ")
      (doseq [alg algs] (print "&"  alg))
      (println)
      (doseq [i (range 1 6)]
        (print (pad-right i 8) "&" (pad-right (get lens i) 8) )
        (doseq [alg algs]
          (let [[secs evals] (get-in res [alg i])]
            (if secs
              (print "&" (pad-right (format-n secs 2) 9) "&" (pad-right (format-n evals 0) 9) )
              (print "&" (pad-right "" 9) "&" (pad-right "" 9)))))      
        (println "\\\\")))))



;(use '[edu.berkeley.ai.util experiments cluster] 'angelic.scripts.experiments-11aaai)
;(run-experiment-set-cluster (make-dm-exp-set))

;; (time (run-experiment-set! (make-dm-lama-exp-set) 6 9))

;; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

