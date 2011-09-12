(ns angelic.scripts.experiments-11ijcai
 (:require [angelic.util :as util]  
	   [angelic.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.domains.sas-problems :as sas-problems]
           [angelic.domains.taxi-constrained :as taxi]           
           [angelic.search.textbook :as textbook]
           [angelic.search.action-set.asplan :as asplan]
           [angelic.search.action-set.stratified :as strat]
           [angelic.search.action-set.ec :as ec]           
	   [angelic.util.experiments :as experiments]))

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
  {:baseline "base"
   :asplan "bi"})

(def taxi-strat-algs
  {:strat "strat"
   :strat+ "strat+"})

(def taxi-ec-algs
  {:ec "EC"})

(def all-taxi-algs (merge taxi-algs (dissoc  taxi-strat-algs :strat+) taxi-ec-algs))

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

(defn make-taxi-strat-exp-set []
   (experiments/make-experiment-set
    "ib-taxi-strat2"
    [:product
     [:size (vec (range 1 11))]
     [:constrain? [true]]
     [:alg (keys taxi-strat-algs)]
     [:type (keys taxi-types)]]    
    (fn [m]
      `((taxi-factories ~(:type m)) 3 3 ~(:size m) ~(:constrain? m) ~(if (= (:type m) :single) 6 1)))
    (fn [m] `(strat/stratified-search ~'init ~(if (= (:alg m) :strat) :simple :fluid)))
    'angelic.scripts.experiments-11ijcai 10 3600 512 false ::ExpResult))

(defn make-taxi-ec-exp-set []
   (experiments/make-experiment-set
    "ib-taxi-ec"
    [:product
     [:constrain? [true]]
     [:alg [:ec]]
     [:union
      [:product [:type [:independent :single]] [:size (vec (range 1 11))]]
      [:product [:type [:pairwise]] [:size (vec (range 2 4))]]]]    
    (fn [m]
      `((taxi-factories ~(:type m)) 3 3 ~(:size m) ~(:constrain? m) ~(if (= (:type m) :single) 6 1)))
    (fn [m] `(ec/ec-search ~'init false false))
    'angelic.scripts.experiments-11ijcai nil #_ 10 3600 512 false ::ExpResult))

(defonce *taxi-results* nil)
(defonce *taxi-single-results* nil)
(defonce *taxi-strat-results* nil)
(defonce *taxi-ec-results* nil)
(defn read-taxi-results []
  (def *taxi-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-exp-set)))))
  (def *taxi-single-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-exp-set-single)))))
  (def *taxi-strat-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-strat-exp-set)))))
  (def *taxi-ec-results* 
       (doall
        (experiments/experiment-set-results->dataset 
         (experiments/read-experiment-set-results (make-taxi-ec-exp-set))))))

(def *alg-order*
     [[[:baseline false] "baseline"]
      [[:baseline true] "baseline+c"]
      [[:strat  true] "{/Symbol \\245}-strat+c"]
      [[:ec true] "EC+c"]
      [[:asplan false] "BIP"]
      [[:asplan true] "BIP+c"]])

(def *alg-order2*
     [[[:baseline false] "baseline"]
      [[:asplan false] "BIP"]
      [[:baseline true] "baseline+c"]
      [[:strat  true] "{/Symbol \\245}-strat+c"]
      [[:ec true] "EC+c"]
      [[:asplan true] "BIP+c"]])

(def *alg-names* (into {} *alg-order*))

(defn order [things key-fn desired-order]
  (let [m (group-by key-fn things)]
    (keep #(first (get m %)) desired-order)))

;;594 665

; Use pdfcrop to remove whitespace
(defn make-taxi-charts []
  (doseq [[type-key [file name]] (take 1 (drop 0 taxi-types))]
    (charts/plot
     (datasets/ds->chart
      (filter (datasets/ds-fn [type output constrain? alg size]
                              (and output (= type type-key) (< size 10)
                                   (if (= type :pairwise)  true #_
                                     constrain?
                                     (or (not constrain?) (#{:baseline :strat :ec} alg)))))              
              (concat (if  (= type-key :single) *taxi-single-results* *taxi-results*)
                      *taxi-ec-results*
                      (remove #(= (:alg %) :strat+) *taxi-strat-results*)))
      [:alg :constrain?] :size :next-count
      {:term "solid dashed size 2.0, 1.5" 
       :ylog true :key (case type-key :independent "top right" :pairwise "bottom right spacing 0.8" :single "bottom right spacing 0.8")
       ;;       :xlabel "# passengers"
       :ylabel (when (= type-key :independent) "# states generated")
       :xrange (if (= type-key :pairwise) "[2:6]" "[1:9]") :yrange "[10:10000000]"
       ;;       :title (str name " taxi")
       :extra-commands [(str "set title \"" name "\" offset 0,-0.8")
                        "set xlabel \"# passengers\" 0,0.5"
                        "set xtics 1"]
       }
      (fn [[alg constrain?]]
        (let [v (cond (and (= alg :asplan) (not constrain?)) 1
                      (= alg :asplan) 4
                      (= alg :strat) 5
                      (= alg :ec) 6
                      constrain? 3
                      :else 2)]
          {:lw 3 :pt v :lt v}))
      *alg-names* 
      (if (= type-key :pairwise)
        #(order % :title (map second *alg-order2*))
        #(order % :title (map second *alg-order*))))
     (str "/Volumes/data/old/Users/jawolfe/Projects/reports/11-ijcai/graphs/" file ".pdf"))))








;(use '[angelic.util experiments cluster] 'angelic.scripts.experiments-11ijcai)
;(run-experiment-set-cluster (make-taxi-strat-exp-set))
