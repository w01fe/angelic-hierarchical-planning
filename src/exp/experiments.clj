(ns exp.experiments
  (:require 
   [edu.berkeley.ai.util :as util]
   [exp [env :as env] [hierarchy :as hierarchy] [taxi :as taxi] [ucs :as ucs] [sahtn-dijkstra :as sd]]
   [edu.berkeley.ai.util [experiments :as experiments]]))



(def *exp-result* ::ExpResult)

(defstruct exp-result 
  :class :experiment :commit-id :timeout? :memout? :output :printed :init-ms :ms :mb
  :next-count :ref-count :plan-count

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
    (env/reset-next-counter)
    (hierarchy/reset-ref-counter)))

(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (struct exp-result ::ExpResult
	  experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
	  (util/sref-get env/*next-counter*)
	  (util/sref-get hierarchy/*ref-counter*)
	  (util/sref-get hierarchy/*plan-counter*)))

(defn make-first-exp-set []
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


(def *cw* 8)
(def *w* (+ 4 (* 3 *cw*)))
(defn make-table [results]
  (let [results (util/group-by #(get-in % [:experiment :parameters :alg]) results)]
    (doseq [alg [:ucs :htn-ucs :nsahtn :sahtn]]
      (let [alg-results (results alg)
            size-map (util/group-by #(get-in % [:experiment :parameters :size]) alg-results)
            sizes    (sort (keys size-map))]
        (println (apply str (pad-right alg 9) "|" (for [s sizes] (str (pad-right s *w*) "|"))))
        (println (apply str (repeat (+ 10 (* (count sizes) (inc *w*))) "-")))
        (doseq [[n-pass pass-maps] (util/group-by #(get-in % [:experiment :parameters :npass]) alg-results)]
                                        ;        (println (util/group-by #(get-in % [:experiment :parameters :size]) pass-maps))
          (println (apply str (pad-right n-pass 9) "|"
                          (for [[exp] (map val (sort-by key (util/group-by #(get-in % [:experiment :parameters :size]) pass-maps)))]
                            (if (:ms exp)
                              (str (pad-right (int (:ms exp)) *cw*) ", " (pad-right (:next-count exp) *cw*) ", " (pad-right (:plan-count exp) *cw*) "|")
                              (apply str (concat (repeat *w* " ") "|"))
                              ))))))    
      (println "\n\n"))))
