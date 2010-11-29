(ns angelic.scripts.experiments-11icaps
 (:require [edu.berkeley.ai [util :as util]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.domains.sas-problems :as sas-problems]
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





(comment
;;;;;;; miconic

 (def miconic-algs
      [[[:baseline] "base"]
       [[:asplan] "bi"]])

 (defn make-exp-set []
   (experiments/make-experiment-set
    "miconic"
    [:product
     [:instance (vec (range 150))]
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
         (experiments/read-experiment-set-results (make-exp-set))))))





;;;;;; charts

(comment
 (def *alg-order* ["H-UCS" "DH-UCS" "DSH-UCS" "AHA*" "DAHA*" "DASHA*"])
 (defn order [things key-fn desired-order]
                                        ;  (println things)
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