(ns edu.berkeley.ai.domains.simple-road-trip
 (:use clojure.test )
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.hybrid-strips :as hs])
 )


; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?

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


(comment 
  (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1)

(let [e (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1)
        as (get-action-space e)]
    (map :name (applicable-actions (get-initial-state e) as)))

(map :name (first (a-star-graph-search (ss-node (make-road-trip-strips-env [['a 3 2] ['b 0 0] ['c 4 2]] '[[a b 2] [a c 1] [c b 1]] 'a 'b 0 4 1)))))
     
  )


(comment 
(deftest simple-hybrid-test
  (let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[b [[a]]]])]
    (is 
     (envs/satisfies-condition?  
       (envs/safe-apply-actions (envs/get-initial-state env)
	  [(hs/get-hs-action env 'get '{?b a ?c table})
	   (hs/get-hs-action env 'up-holding '{?b a ?ngy 4})
	   (hs/get-hs-action env 'right-holding '{?b a ?ngx 5})
	   (hs/get-hs-action env 'put '{?b a ?c b})])
       (envs/get-goal env)))))

)
