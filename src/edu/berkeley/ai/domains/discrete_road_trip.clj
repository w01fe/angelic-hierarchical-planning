(ns edu.berkeley.ai.domains.discrete-road-trip
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
 )


; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?

(def *drt-hierarchy* "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/discrete_road_trip.hierarchy")


(let [f (util/path-local "discrete_road_trip.pddl")]
  (defn make-discrete-road-trip-strips-domain []
    (strips/read-strips-planning-domain f)))
 		
(defn- medians [min max]
  (when (< min max)
    (let [s      (+ min max)
	  median (/ (if (odd? s) (inc s) s) 2)]
      (cons ['median min median max]
	    (concat
	     (medians min (dec median))
	     (medians median max))))))
		  
(defn make-discrete-road-trip-strips-env 
  [city-gas-prices edges start end init-gas max-gas]
    (strips/make-strips-planning-instance 
     "discrete-road-trip"
     (make-discrete-road-trip-strips-domain)
     {'loc (map key city-gas-prices)
      'gas (range (inc max-gas))}  
     (set (concat 
	   [['at start] ['gas init-gas] ['max-gas max-gas] ['zero 0] ['one-greater max-gas max-gas]] 
	   (for [[f t l] edges] ['road-length f t l])
	   (for [[l p] city-gas-prices :when p] [(util/symbol-cat 'has-gas p) l])
	   (for [x (range max-gas)] ['one-greater (inc x) x])
	   (for [x1 (range (inc max-gas)), x2 (range (inc max-gas))] ['overflow-sum x1 x2 (min (+ x1 x2) max-gas)])
	   (for [s (range (inc max-gas)), x (range (inc s))] ['sum x (- s x) s])
	   (for [x1 (range (inc max-gas)), x2 (range (inc x1))] ['geq x1 x2])
	   (medians 0 max-gas)))
     [['at end]]
     (fn [s] 
       (format "At %s with %s gas." 
	       (some #(when (= (first %) 'at) (second %)) s)
	       (some #(when (= (first %) 'gas) (second %)) s)))
     ))


(comment 


(interactive-search (alt-node (get-hierarchy *drt-hierarchy* (constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b 1 c nil d 3} '[[a b 1] [b c 3] [c d 6]] 'a 'd 0 16))) (make-first-maximal-choice-fn '{act 10 next-stop1 9 next-stop2 9 next-stop3 9 fill-up1 8 fill-up2 8 fill-up3 8 drive-to 8})))


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
