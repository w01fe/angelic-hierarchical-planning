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


;;;;;;;;;;;;;;;;;; Helpers - parsing LAMA output ;;;;;;;;;;;;;;;;;;;;;;;;;


(def alg-forms
     {:sahtn   (fn [m] `(sahtn/sahtn ~'init #{:nav :reach :discretem-tla}))
      :aha*    (fn [m] `(aha/ah-a* ~'init true))
      :dash-a* (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                                  :choice-fn rand-nth))})


(defn line-match [^String s ^String prefix]
  (when (.startsWith s prefix)
    (.substring s (int (.length prefix)))))

(defn lm-read [^String s ^String prefix]
  (let [^String suffix (line-match s prefix)]
    (assert suffix)
    (read-string suffix)))


(defn parse-lama-output [s]
  (let [lines (seq (.split ^String s "\n"))
        parts (partition-by #(.startsWith ^String % "Solution found!") lines)]
    (when (> (count parts) 1)
      (let [[sol rest] (split-with #(not (.startsWith ^String % "Plan length")) (last parts))            
            [marker expanded generated search total] (take-last 5 rest)]
        (assert (line-match marker "Completely"))
        {:solution sol
         :solution-length (lm-read (first rest) "Plan length:")
         :solution-cost   (read-string (last (.split ^String (first rest) " ")))
         :expanded (lm-read expanded "Expanded")
         :generated (lm-read generated "Generated")
         :last-search-seconds (lm-read search "Search time:")
         :last-total-seconds (lm-read total "Total time:")}))))


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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Discrete manipulation experiments ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

(defn make-dm-lama-exp-set []
  (experiments/make-experiment-set "11aaai-dm-lama"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:rand    [1 2 3]]
     [:alg     [:lama]]]
    (fn [m]
      `(dm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m)))
    (fn [m] `(dm/solve-dmh-lama ~'init))
    'angelic.scripts.experiments-11aaai nil 3600 512 false ::ExpResult))

(defmacro defresults [name es-maker]
  (let [sn (util/symbol-cat '* name '-results*)]
    `(do (defonce ~sn nil)
         (defn ~(util/symbol-cat 'read- name '-results) []
           (def ~sn
                (experiments/experiment-set-results->dataset
                 (experiments/read-experiment-set-results (~es-maker))))))))

(defresults dm make-dm-exp-set)
(defresults dm-lama make-dm-lama-exp-set)


(defn read-all-results [] (read-dm-results) (read-dm-lama-results))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Discrete charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn make-dm-charts 
  ([] (make-dm-charts "/Users/jawolfe/Projects/reports/11-aaai/graphs/"))
  ([dir]
     (doseq [[n ylabel field] [["evals" "\\# of evaluations" :opt-count]
                               ["time"  "runtime (s)" :secs]]]
       (-> (datasets/ds-summarize
            (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms *dm-results*) :secs)
            [:objects :alg] [[field util/mean field]])
           (datasets/ds->chart
            [:alg] :objects field
            {:term "solid dashed size 2.0,1.5"
             :ylog  "t" :xrange "[1:5]" ;             :yrange "[4:600]"
             :title "discrete pick-and-place problems" :key "on" #_"at 2.6, 445"
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
                    (group-by inst-name exps)))
   (group-by :alg
             (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)
            
             #_(datasets/ds-summarize
                (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)
                [:objects :alg] [[:secs util/mean :secs] [:opt-count util/mean :opt-count]]))))

(defn dm-solution-lengths []
  (into {}
   (map (juxt inst-name #(count (first (:output %))))
        (filter #(and (= (:alg %) :dash-a*) (:ms %)) *dm-results*))))


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
        lens (dm-solution-lengths)
        algs [:lama :aha* :sahtn :dash-a*]]
    (print "num & len ")
    (doseq [alg algs] (print "&"  alg))
    (println)
    (doseq [i (range 1 6) r (range 1 4)]
      (let [inst (inst-name {:objects i :rand r})]
       (print (pad-right inst 8) "&" (pad-right (get lens inst) 8) "&")
       (doseq [alg algs]
         (let [[secs evals] (get-in res [alg inst])]
           (if secs
             (print (pad-right (format-n secs 2) 9) "&" (pad-right (format-n evals 0) 9) "&")
             (print (pad-right "" 9) "&" (pad-right "" 9) "&"))))      
       (println)))))



;(use '[edu.berkeley.ai.util experiments cluster] 'angelic.scripts.experiments-11aaai)
;(run-experiment-set-cluster (make-dm-exp-set))

;; (time (run-experiment-set! (make-dm-lama-exp-set) 6 9))

;; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

