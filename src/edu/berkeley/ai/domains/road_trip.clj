(ns edu.berkeley.ai.domains.road-trip
; (:import [java.util HashMap HashSet])
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.hybrid-strips :as hs])
 )


; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?


(let [f (util/path-local "road_trip.pddl")]
  (defn make-road-trip-strips-domain []
    (hs/read-hybrid-strips-planning-domain f)))
 				  

(defn make-road-trip-strips-env 
  "Stacks is a forest of block info items (Table goes from -1 to 0 h, implicit).
   Each item is [block l-offset c-dist width height on-items].  Goal-stacks is same without numeric info."
  ([city-gas-prices edges start end init-gas tank-size]
     (make-road-trip-strips-env city-gas-prices edges start end init-gas tank-size  nil))
  ([city-gas-prices edges start end init-gas tank-size discrete-grid-size]
    (hs/make-hybrid-strips-planning-instance 
     "road-trip"
     (make-road-trip-strips-domain)
     {'loc (map first city-gas-prices)}
     (set (concat 
	   [['at start]] 
;	   (for [[c g p] city-gas-prices :when (> g 0)] ['has-gas c])
	   (for [[f t l] edges] ['road-between f t])))
     (assoc (into {} (concat (util/forcat [[c g p] city-gas-prices]
					  [[['gas-at c] g] [['gas-price c] p]])
			     (for [[f t l] edges] [['road-length f t] l]))) 			             '[gas] init-gas
       '[tank-size] tank-size)
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
(util/deftest simple-hybrid-test
  (let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[b [[a]]]])]
    (util/is 
     (envs/satisfies-condition?  
       (envs/safe-apply-actions (envs/get-initial-state env)
	  [(hs/get-hs-action env 'get '{?b a ?c table})
	   (hs/get-hs-action env 'up-holding '{?b a ?ngy 4})
	   (hs/get-hs-action env 'right-holding '{?b a ?ngx 5})
	   (hs/get-hs-action env 'put '{?b a ?c b})])
       (envs/get-goal env)))))

)
