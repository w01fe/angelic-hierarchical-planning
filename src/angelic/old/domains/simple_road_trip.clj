(ns angelic.old.domains.simple-road-trip
 (:use clojure.test )
 (:require [angelic.util :as util] [angelic.old  [envs :as envs]] 
           [angelic.old.envs.hybrid-strips :as hs])
 )

; simple-road-trip is like road-trip but tank size is always 100, 
; every city sells gas (at some price).  

;; How hard is this?  it's a DP over city x gas.
;; You always want to either buy nothing, fill up, or get just enough to reach
;; a city with cheaper gas.  

; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?

;; TODO: make regular road trip be this one but with multiple place goals allowed.  

;; A good heuristic is: ?


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

(def *simple-road-trip-hierarchy* (util/path-local "simple_road_trip.hierarchy"))







(comment 

(time  (let [e (make-simple-road-trip-strips-env '{a 5 b 0 c 20 z 10} '[[a z 100] [z b 30] [a c 90] [c b 20]] 'a 'b 0) [s r] (time  (a-star-search (alt-node (get-hierarchy *simple-road-trip-hierarchy* e) {:cache? false :graph? false :ref-choice-fn first-choice-fn})))]
               [ (map :name (extract-hybrid-primitive-solution e s)) r]))
)