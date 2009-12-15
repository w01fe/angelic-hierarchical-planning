(ns exp.experiments
  (:require 
   [edu.berkeley.ai.util :as util]
   [exp [env :as env] [hierarchy :as hierarchy] [taxi :as taxi] [ucs :as ucs] [sahtn-dijkstra :as sd]]
   [edu.berkeley.ai.util [experiments :as experiments] [charts :as charts] [datasets :as datasets]]))



(def *exp-result* ::ExpResult)

(defstruct exp-result 
  :class :experiment :commit-id :timeout? :memout? :output :printed :init-ms :ms :mb
  :next-count :ref-count :plan-count)

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
  (env/reset-next-counter)
  (hierarchy/reset-ref-counter))

(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (util/prln 
   (struct exp-result ::ExpResult
           experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
           (util/sref-get env/*next-counter*)
           (util/sref-get hierarchy/*ref-counter*)
           (util/sref-get hierarchy/*plan-counter*))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Taxi ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-taxi-exp-set []
  (experiments/make-experiment-set "simple-taxi"
    [:product
     [:size [5 50]#_[2 5 10] #_[2 5 10 20]]
     [:npass [1 2 4 6 8 10 12 14] #_[1 2 5 10]]
     [:alg [:ucs :htn-ucs :nsahtn :sahtn]]]; 
    (fn [m]
      (let [e `(taxi/make-random-taxi-env ~(:size m) ~(:size m) ~(:npass m) 0)]
        (condp = (:alg m)
          :ucs     e
          :htn-ucs `(hierarchy/ShopHTNEnv (taxi/simple-taxi-hierarchy ~e))
          :sahtn   `(taxi/simple-taxi-hierarchy ~e)
          :nsahtn   `(taxi/simple-taxi-hierarchy-nsa ~e)
          )))
    (fn [m]
      (condp = (:alg m)
        :ucs      `(ucs/uniform-cost-search ~'init)
        :htn-ucs  `(ucs/uniform-cost-search ~'init)
        :sahtn    `(sd/sahtn-dijkstra ~'init)
        :nsahtn    `(sd/sahtn-dijkstra ~'init)
        ))
    'exp.experiments 20 10000 512 false  ::ExpResult))

(defn pad-right [x n]  
  (let [xs (str x) 
        s #^String (str "                               " xs)]
    (assert (<= (.length xs) n))
    (.substring s (- (.length s) n)))) 


(defn read-taxi-results []
  (def *taxi-results* 
       (experiments/experiment-set-results->dataset 
        (experiments/read-experiment-set-results (make-taxi-exp-set)))))

(def *cw* 8)
(def *w* (+ 4 (* 3 *cw*)))
(defn make-taxi-table []
  (let [results (util/group-by #(get-in % [:alg]) *taxi-results*)]
    (doseq [alg [:ucs :htn-ucs :nsahtn :sahtn]]
      (let [alg-results (results alg)
            size-map (util/group-by #(get-in % [ :size]) alg-results)
            sizes    (sort (keys size-map))]
        (println (apply str (pad-right alg 9) "|" (for [s sizes] (str (pad-right s *w*) "|"))))
        (println (apply str (repeat (+ 10 (* (count sizes) (inc *w*))) "-")))
        (doseq [[n-pass pass-maps] (util/group-by #(get-in % [ :npass]) alg-results)]
                                        ;        (println (util/group-by #(get-in % [:experiment :parameters :size]) pass-maps))
          (println (apply str (pad-right n-pass 9) "|"
                          (for [[exp] (map val (sort-by key (util/group-by #(get-in % [ :size]) pass-maps)))]
                            (if (:ms exp)
                              (str (pad-right (int (:ms exp)) *cw*) ", " (pad-right (:next-count exp) *cw*) ", " (pad-right (second (:output exp)) #_(:plan-count exp) *cw*) "|")
                              (apply str (concat (repeat *w* " ") "|"))
                              ))))))    
      (println "\n\n"))))








(defn make-taxi-charts 
  ([] (make-taxi-charts "/Users/jawolfe/Projects/reports/10-icaps/figs/"))
  ([dir] 
     (charts/plot 
      (datasets/ds->chart
       (datasets/ds-derive #(/ (:ms %) 1000) (filter (datasets/ds-fn [ms size] (and ms (= size 50))) *taxi-results*) :secs)
       [:alg] :npass :secs 
       {:term "solid dashed size 3,1.7"  :ylog "t" :xrange "[1:14]" :yrange "[0.3:1000]"
        :title "50x50 taxi problems" :key "bottom right"
       ; :xlabel "# of passengers"         :ylabel "runtime (s)"
        :extra-commands ["set ylabel \"runtime(s)\" -2,0"]
        } 
       (let [c (util/counter-from 0)] (fn [& args] (let [v ([1 2 3 6] (c))]  {:lw 3 :pt v :lt v})))
       {[:ucs] "UCS" [:htn-ucs]  "H-UCS" [:sahtn] "SAHTN" [:nsahtn] "N-SAHTN"}
       (fn [l] (sort-by #(if (=  "UCS" (:title %)) "Q" (:title  %)) l)))
      (str dir "taxi-50-time.pdf"))
     (charts/plot 
      (datasets/ds->chart
       (datasets/ds-derive #(/ (:ms %) 1000) (filter (datasets/ds-fn [ms size] (and ms (= size 50))) *taxi-results*) :secs)
       [:alg] :npass :next-count 
       {:term "solid dashed size 3,1.2"  :ylog "t" :xrange "[1:14]" ;:yrange "[0.3:1000]"
      ;  :title "Primitive action applications for 50x50 taxi problems" 
        :key "top right"
        :xlabel "# of passengers" :ylabel "# of primitive applications"
        } 
       (let [c (util/counter-from 0)] (fn [& args] (let [v ([1 2 3 6] (c))]  {:lw 3 :pt v :lt v})))
       {[:ucs] "UCS" [:htn-ucs]  "H-UCS" [:sahtn] "SAHTN" [:nsahtn] "N-SAHTN"}
       (fn [l] (sort-by #(if (=  "UCS" (:title %)) "Q" (:title  %)) l)))
      (str dir "taxi-50-prims.pdf"))               
     ))