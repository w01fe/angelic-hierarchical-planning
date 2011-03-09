(ns angelic.scripts.experiments-11aaai
 (:require [angelic.util :as util]  
	   [angelic.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.search.textbook :as textbook]
           [angelic.domains.discrete-manipulation :as dm]
           [angelic.domains.nav-switch :as ns]           
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


(defn median-of [n items]
  (assert (odd? n))
  (let [ind (quot n 2)]
    (when (> (count items) ind)    
      (nth (sort items) ind))))

(defn solution-lengths [ds k nper]
  (util/map-vals (fn [es] (median-of nper (map #(count (first (:output %))) es)))
                 (group-by k
                  (filter #(and (= (:alg %) :dash-a*) (:ms %)) ds))))

(defn pad-right [x n]  
  (let [xs (str x) 
        s #^String (str "                               " xs)]
    (assert (<= (.length xs) n))
    (.substring s (- (.length s) n))))

(defn format-n [n dec]
  (let [base (util/expt 10 dec)]
    (/ (int (* base n)) (if (> dec 0) (double base) 1))))


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
;;;;;;;;;;;;;;;;;;;;;;;; Nav Switch experiments ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def +ns-sizes+ [5 10 20 50 100 200 500])

(defn make-ns-exp-set []
  (experiments/make-experiment-set "11aaai-ns"
    [:product
     [:size   +ns-sizes+]
     [:alg    (keys alg-forms)]
     [:rand   [0 1 2]]]
    (fn [m]
      `(ns/make-nav-switch-hierarchy
        (ns/make-random-nav-switch-env ~(:size m) 20 ~(:rand m)) true))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.experiments-11aaai nil #_ 10 3600 512 false ::ExpResult))

(defn make-ns-dd-exp-set []
  (experiments/make-experiment-set "11aaai-ns-dd"
    [:product
     [:size   +ns-sizes+]
     [:alg    [:dash-a*-dijkstra]]
     [:rand   [0 1 2]]]
    (fn [m]
      `(ns/make-nav-switch-hierarchy
        (ns/make-random-nav-switch-env ~(:size m) 20 ~(:rand m)) true))
    (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                       :choice-fn rand-nth :dijkstra #{'~'navv '~'navh}))
    'angelic.scripts.experiments-11aaai nil #_ 10 3600 512 false ::ExpResult))

(defresults ns make-ns-exp-set)
(defresults ns-dd make-ns-dd-exp-set)


;; DASH-A* blows the stack on the cluster for no good reason, so I'm running
;; those experiments locally.

#_ (let [es (make-ns-exp-set)]
     (doseq [[i e] (indexed es)]
      (when (= (:alg (:parameters e)) :dash-a*)
        (run-experiment-set! es i (inc i)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  NS charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn make-ns-charts 
  ([] (make-ns-charts "/Users/jawolfe/Projects/reports/11-aaai/graphs/"))
  ([dir]
     (doseq [[n ylabel field] [["evals" "\\# of evaluations" :opt-count]
                               ["time"  "runtime (s)" :secs]]]
       (-> (datasets/ds-summarize
            (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms *ns-results*) :secs)
            [:size :alg] [[field (fn [& args] (median-of 3 args)) #_util/mean field]])
           (datasets/ds->chart
            [:alg] :size field
            {:term "solid dashed size 2.0,1.5"
             :ylog  "t"  :xlog "t" :xrange "[5:500]" ;             :yrange "[4:600]"
             :title "nav-switch problems" :key "bottom right" #_"at 2.6, 445"
             :xlabel "grid size (side length)"
             :extra-commands [(str "set ylabel \"" ylabel "\" -2,0") #_ "set xtics 1"]}            
            (let [c (util/counter-from 0)] (fn [& args] (let [v ([1 2 3 6] (c))]  {:lw 3 :pt v :lt v})))
            identity #_{[:ucs] "UCS" [:htn-ucs]  "H-UCS" [:sahtn] "SAHTN" [:nsahtn] "N-SAHTN"}
            identity #_(fn [l] (sort-by #(if (=  "UCS" (:title %)) "Q" (:title  %)) l)))
           (charts/plot (str dir "ns-" n ".pdf"))))))


(defn make-ns-table []
  (let [res  (util/map-vals
              (fn [exps]
                (util/map-vals (fn [es] (assert (= (count es) 1)) ((juxt :secs :opt-count) (first es)))
                               (group-by :size exps)))
              (group-by :alg                       
                        (datasets/ds-summarize
                         (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms (concat *ns-results* *ns-dd-results*)) :secs)
                         [:size :alg] [[:secs #(median-of 3 %&) :secs] [:opt-count #(median-of 3 %&) :opt-count]])))
        lens (solution-lengths *ns-results* :size 3)
        algs [:lama  :sahtn :aha* #_ :dash-a* :dash-a*-dijkstra]]
    (print "num & len ")
    (doseq [alg algs] (print "&"  alg))
    (println)
    (doseq [s +ns-sizes+]
      (print (pad-right s 8) "&" (pad-right (get lens s) 8) )
      (doseq [alg algs]
        (let [[secs evals] (get-in res [alg s])]
          (if secs
            (print "&" (pad-right (format-n secs 2) 9) "&" (pad-right (format-n evals 0) 9))
            (print "&" (pad-right "" 9) "&" (pad-right "" 9)))))      
      (println "\\\\"))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Discrete manipulation experiments ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-dm-exp-set []
  (experiments/make-experiment-set "11aaai-dm"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:alg     (keys alg-forms)]
     [:rand    [0 1 2 3 4]]]
    (fn [m]
      `(dm/make-discrete-manipulation-hierarchy
        (dm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m))))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.experiments-11aaai 10 3600 1024 false ::ExpResult))

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
(defn dm-result-map [ds n]
  (util/map-vals
   (fn [exps]
     (util/map-vals (fn [es] (assert (= (count es) 1)) ((juxt :secs :opt-count) (first es)))
                    (group-by :objects #_ inst-name exps)))
   (group-by :alg
            #_ (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)            
             (datasets/ds-summarize
              (datasets/ds-derive #(/ (:ms %) 1000) (filter :ms ds) :secs)
              [:objects :alg] [[:secs #(median-of n %&) :secs] [:opt-count #(median-of n %&) :opt-count]]))))

#_(defn dm-solution-lengths []
  (into {}
   (map (juxt inst-name #(count (first (:output %))))
        (filter #(and (= (:alg %) :dash-a*) (:ms %)) *dm-results*))))




(defn make-dm-table []
  (let [res (merge (dm-result-map *dm-results* 5) (dm-result-map (parsed-lama) 5))
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
      (println "\\\\"))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Continuous manipulation experiments ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn make-cm-exp-set []
  (experiments/make-experiment-set "11aaai-cm"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:alg     (keys alg-forms)]
     [:rand    [0 1 2]]]
    (fn [m] `(identity 'dummy))
    (fn [m] `(identity 'dummy))
    'angelic.scripts.experiments-11aaai nil 3600 512 false ::ExpResult))

(defresults cm make-cm-exp-set)

(defn make-cm-table []
  (let [res (dm-result-map *cm-results* 3)
        lens (solution-lengths *cm-results* :objects 3)
        algs [:lama :sahtn :aha* :dash-a*]] (println res)
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
      (println "\\\\"))))




;(use '[angelic.util experiments cluster] 'angelic.scripts.experiments-11aaai)
;(run-experiment-set-cluster (make-dm-exp-set))

;; (time (run-experiment-set! (make-dm-lama-exp-set) 6 9))

;; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

