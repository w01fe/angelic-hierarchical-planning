(ns edu.berkeley.ai.domains.simple-road-trip
 (:use clojure.test )
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.hybrid-strips :as hs])
 )

; simple-road-trip is like road-trip but tank size is always 100, 
; every city sells gas (at some price).  

; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?

;; TODO: make regular road trip be this one but with multiple place goals allowed.  

(let [f (util/path-local "simple_road_trip.pddl")]
  (defn make-simple-road-trip-strips-domain []
    (hs/read-hybrid-strips-planning-domain f)))
 				  

(defn make-simple-road-trip-strips-env 
  ([city-gas-prices edges start end init-gas]
     (make-simple-road-trip-strips-env city-gas-prices edges start end init-gas nil))
  ([city-gas-prices edges start end init-gas discrete-grid-size]
    (hs/make-hybrid-strips-planning-instance 
     "simple-road-trip"
     (make-simple-road-trip-strips-domain)
     {'loc (map key city-gas-prices)}
     (set (concat 
	   [['at start]] 
	   (for [[f t l] edges] ['road-between f t])))
     (assoc (into {} (concat (util/forcat [[c p] city-gas-prices]
					  [[['gas-price c] p]])
			     (for [[f t l] edges] [['road-length f t] l]))) 
       '[gas] init-gas)
     [['at end]]
     (fn [[d n]] 
       (format "At %s with %s gas." 
	       (some #(when (= (first %) 'at) (second %)) d )
	       (get n '[gas])))
     discrete-grid-size
     )))


(require '[edu.berkeley.ai.search.algorithms.textbook :as algs] 
	 '[edu.berkeley.ai.search.state-space :as ss])

(deftest simple-road-trip-test
  (let [args  '[ {a 3 b 3} [[a b 2]] a b 1]]
    (doseq [[e s] (map vector (map #(apply make-simple-road-trip-strips-env %) [args (conj args 1)]) [-299 -5])]
      (is (= s (second (algs/a-star-graph-search (ss/ss-node e)))))))
  (let [args  [ '{a 3 b 0 c 4} '[[a b 2] [a c 1] [c b 1]] 'a 'b 0 ]]
    (doseq [[e s] (map vector (map #(apply make-simple-road-trip-strips-env %) [args (conj args 1)]) [-302 -8])]
      (is (= s (second (algs/a-star-graph-search (ss/ss-node e))))))))





