(ns angelic.scripts.experiments-11icaps
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.domains.sas-problems :as sas-problems]
           [angelic.domains.taxi-constrained :as taxi]           
           [angelic.search.textbook :as textbook]
           [angelic.search.action-set.asplan :as asplan]
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

;;;;;;; logistics

(def algs
  [[[:baseline] "base"]
   [[:asplan] "bi"]
   [[:asplan :directed? false] "bi-d"]
   [[:asplan :greedy? false] "bi-g"]
   [[:asplan :deadlock? false] "bi-dl"]
   [[:asplan :dead-vars? false] "bi-dv"]])

(defn make-exp-set []
  (experiments/make-experiment-set
   "logistics"
   [:product
    [:instance (vec (range 27))]
    [:alg (map first algs)]]
   (fn [m]
     (let [{[type & args] :alg instance :instance} m
           instance-form `(force (nth sas-problems/ipc2-logistics ~instance))]
       (if (= type :baseline)
         instance-form
         `(asplan/make-asplan-env ~instance-form ~@args))))
   (fn [m] `(textbook/uniform-cost-search ~'init))
   'angelic.scripts.experiments-11icaps 10 600 512 false ::ExpResult))

(defonce *results* nil)
(defn read-results []
  (def *results* 
       (experiments/experiment-set-results->dataset 
        (experiments/read-experiment-set-results (make-exp-set)))))

;;;;;;; table

(defn pad-right [x n]  
    (let [xs (str x) 
          s #^String (str "                               " xs)]
      (assert (<= (.length xs) n))
      (.substring s (- (.length s) n)))) 

(defn prob-name [^String x]
  (.substring x 14 (- (count x) 5)))



(def *cw* 8)
(def *w* (+ 4 (* 3 *cw*)))
(defn make-full-table []
  (println (apply str (pad-right " " 9) "|" (for [[_ alg] algs] (str (pad-right alg *w*) "|"))))
  (doseq [i (range 25)]
    (print (str (prob-name (nth sas-problems/ipc2-logistics-names i)) "   "  " " "|"))
    (doseq [[algg name] algs
            :let [result (util/find-first (datasets/ds-fn [instance alg] (and (= instance i) (= alg algg))) *results*)]]
      (print (str (pad-right (if (:output result) (str " " (pad-right (:next-count result) *cw*) (pad-right  (int (:ms result)) *cw*)) (str ">" (:next-count result))) *w*) "|" )))
    (println) ))

(defn make-table []
  (println (apply str (pad-right " " 9) "|" (for [[_ alg] algs] (str (pad-right alg *w*) "|"))))
  (doseq [[i reward] (sort-by second (map (juxt identity #(- (second (:output (util/find-first (datasets/ds-fn [instance] (= instance %)) *results*))))) (range 10)))]
    (print (str (prob-name (nth sas-problems/ipc2-logistics-names i)) "   " (pad-right reward 2) " " "|"))
    (doseq [[algg name] algs
            :let [result (util/find-first (datasets/ds-fn [instance alg] (and (= instance i) (= alg algg))) *results*)]]
      (print (str (pad-right (if (:output result) (str " " (pad-right (:next-count result) *cw*) (pad-right  (int (:ms result)) *cw*)) (str ">" (:next-count result))) *w*) "|" )))
    (println) ))

(defn make-latex-table []
  (println (apply str (pad-right " " 9) "&" (for [[_ alg] algs] (str (pad-right alg (/ *w* 2)) " &"))))
  (doseq [[i reward] (sort-by second (map (juxt identity #(- (second (:output (util/find-first (datasets/ds-fn [instance] (= instance %)) *results*))))) (range 10)))]
    (print (str (prob-name (nth sas-problems/ipc2-logistics-names i)) " & " (pad-right reward 2) " " "&"))
    (doseq [[algg name] algs
            :let [result (util/find-first (datasets/ds-fn [instance alg] (and (= instance i) (= alg algg))) *results*)]]
      (print (str (str " " (pad-right (:next-count result) *cw*) " & " (pad-right  (int (:ms result)) *cw*)) " & " )))
    (println) ))


;;;;; Taxi

(def taxi-algs
  {:baseline "base"
   :asplan "bi"})

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
    "ib-taxi"
    [:product
     [:run        [1  ]]
     [:size (vec (range 1 16))]
     [:constrain? [true false]]
     [:alg (      keys taxi-algs)]
     [:type (keys taxi-types)]]    
    (fn [m]
      (let [instance-form `((taxi-factories ~(:type m)) 3 3 ~(:size m) ~(:constrain? m) ~(:run m))]
        (if (= (:alg m) :baseline)
          instance-form
          `(asplan/make-asplan-env ~instance-form))))
    (fn [m] `(textbook/uniform-cost-search ~'init))
    'angelic.scripts.experiments-11icaps 10 3600 512 false ::ExpResult))

(defn make-taxi-exp-set-single []
   (experiments/make-experiment-set
    "ib-taxi-single"
    [:product
     [:run        [6]]
     [:size (vec (range 1 11))]
     [:constrain? [true false]]
     [:alg (      keys taxi-algs)]
     [:type [:single]]]    
    (fn [m]
      (let [instance-form `((taxi-factories ~(:type m)) 3 3 ~(:size m) ~(:constrain? m) ~(:run m))]
        (if (= (:alg m) :baseline)
          instance-form
          `(asplan/make-asplan-env ~instance-form))))
    (fn [m] `(textbook/uniform-cost-search ~'init))
    'angelic.scripts.experiments-11icaps 10 3600 512 false ::ExpResult))



(defonce *taxi-results* nil)
(defonce *taxi-single-results* nil)
(defn read-taxi-results []
  (def *taxi-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-exp-set)))))
  (def *taxi-single-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-exp-set-single))))))

(comment(def *alg-order*
      [[[:baseline false] "Baseline"]
       [[:baseline true] "Baseline + constraint"]
       [[:asplan false] "Bounded Intention"]
       [[:asplan true] "Bounded Intention + constraint"]]))


(def *alg-order*
     [[[:baseline false] "baseline"]
      [[:baseline true] "baseline+c"]
      [[:asplan false] "BI"]
      [[:asplan true] "BI+c"]])

(def *alg-names* (into {} *alg-order*))

(defn order [things key-fn desired-order]
  (let [m (group-by key-fn things)]
    (keep #(first (get m %)) desired-order)))

; Use pdfcrop to remove whitespace
(defn make-taxi-charts []
  (doseq [[type-key [file name]] taxi-types]
    (charts/plot
     (datasets/ds->chart
      (filter (datasets/ds-fn [type output constrain? alg]
                              (and output (= type type-key)
                                   (if (= type :pairwise) true #_
                                     constrain?
                                     (or (not constrain?) (= alg :baseline)))))              
              (if  (= type-key :single) *taxi-single-results* *taxi-results*))
      [:alg :constrain?] :size :next-count
      {:term "solid dashed size 2.0, 1.5" 
       :ylog true :key (if (= type-key :independent) "top right" "bottom right")
       ;;       :xlabel "# passengers"
       :ylabel (when (= type-key :independent) "# states to optimal")
       :xrange (if (= type-key :pairwise) "[1:6]" "[1:10]") :yrange "[10:10000000]"
       ;;       :title (str name " taxi")
       :extra-commands [(str "set title \"" name "\" offset 0,-0.8")
                        "set xlabel \"# passengers\" 0,0.5"]
       }
      (fn [[alg constrain?]] (let [v (cond (and (= alg :asplan) (not constrain?)) 1 (= alg :asplan) 4 constrain? 3 :else 2)] {:lw 3 :pt v :lt v}))
      *alg-names*  #_ #(let [n (first %)] (if (= (last n) \U) (apply str (concat (drop-last n) "-UCS")) (str n "*")))
      #(order % :title (map second *alg-order*)))
     (str "/Users/jawolfe/Projects/reports/11-icaps/graphs/" file ".pdf"))))




;;;;;; charts

(comment
 (def *alg-order* ["H-UCS" "DH-UCS" "DSH-UCS" "AHA*" "DAHA*" "DASHA*"])
 (defn order [things key-fn desired-order]
   (let [m (group-by key-fn things)]
     (map #(first (util/safe-get m %)) desired-order)))

 (defn make-charts
   ([] (make-charts "/Users/jawolfe/Projects/reports/10-aaai-btamp/poster/figs/" ))
   ([dir]
      (charts/plot 
       (datasets/ds->chart 
        (datasets/ds-derive #(/ (:ms %) 1000) (filter (datasets/ds-fn [ms] (and ms)) *results*) :secs) 
        [:alg] :objects :secs 
        {:term "solid dashed size 2.4,1.3"   :ylog nil :xrange "[1:6]" :yrange "[0:60]"
                                        ;        :title "discrete manipulation problems" :xlabel "# of objects" ;:ylabel "runtime (s)"
         :key "at 4.8, 67 height 3"                    
         :extra-commands ["set ylabel \"runtime(s)\" 1,0"
                          "set xlabel \"# of objects\" 0,.5"]} 
        (let [c (util/counter-from 0)] (fn [& args] (let [v ([2 3 1 5 4.8 6] (c))]  {:lw 3 :pt v :lt v})))
        #(let [n (first %)] (if (= (last n) \U) (apply str (concat (drop-last n) "-UCS")) (str n "*")))
        #(order % :title *alg-order*))
       (str dir "dm-time.pdf") false)
      #_ (charts/plot 
          (datasets/ds->chart 
           (datasets/ds-derive #(/ (:ms %) 1000) (filter (datasets/ds-fn [ms] (and ms)) *results*) :secs) 
           [:alg] :objects :next-count 
           {:term "solid dashed size 3,1.7"   :ylog nil :xrange "[1:6]" :yrange "[0:60000]"  :key "at 3.6,57000"
                                        ;   :title "discrete manipulation problems"
            :extra-commands ["set ylabel \"# of primitive action evaluations(s)\" 1,0"
                             "set xlabel \"# of objects\" 0,.5"]} 
           (let [c (util/counter-from 0)] (fn [& args] (let [v ([1 2 3 6 5 4] (c))]  {:lw 3 :pt v :lt v})))
           first #(order % :title *alg-order*))
          (str dir "dm-prim.pdf") false)
      ))


;(use '[edu.berkeley.ai.util experiments cluster] 'angelic.aaai10)
;(run-experiment-set-cluster (make-exp-set))

; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

)