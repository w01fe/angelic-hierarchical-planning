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
  [city-gas-prices edges start dests init-gas max-gas]
  (println city-gas-prices edges start dests init-gas max-gas)
    (strips/make-strips-planning-instance 
     "discrete-road-trip"
     (make-discrete-road-trip-strips-domain)
     {'loc (map key city-gas-prices)
      'gas (range (inc max-gas))}  
     (set (concat 
	   [['at start] ['visited start] ['gas init-gas] ['max-gas max-gas] ['zero 0] ['one-greater max-gas max-gas]] 
	   (for [[f t l] edges] ['road-length f t l])
	   (for [[l p] city-gas-prices :when p] [(util/symbol-cat 'has-gas p) l])
	   (for [x (range max-gas)] ['one-greater (inc x) x])
	   (for [x1 (range (inc max-gas)), x2 (range (inc max-gas))] ['overflow-sum x1 x2 (min (+ x1 x2) max-gas)])
	   (for [s (range (inc max-gas)), x (range (inc s))] ['sum x (- s x) s])
	   (for [x1 (range (inc max-gas)), x2 (range (inc x1))] ['geq x1 x2])
	   (medians 0 max-gas)))
     (for [d dests] ['visited d])
     (fn [s] 
       (format "At %s with %s gas." 
	       (some #(when (= (first %) 'at) (second %)) s)
	       (some #(when (= (first %) 'gas) (second %)) s)))
     ))

; Note; use of ICAPS choice fn is essential for good perf.

(def *road-trip* (strips/constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b 1 c nil d 3} '[[a b 1] [b c 3] [c d 6]] 'a 'd 0 16)))

(defn make-random-discrete-road-trip-strips-env [n-cities max-gas nogas-p edge-p]
  (util/assert-is (> n-cities 1))
  (make-discrete-road-trip-strips-env
   (into {}
	 (for [c (range n-cities)] [(util/symbol-cat 'city c) 
				    (when-not (util/rand-bool nogas-p)
				      (util/rand-elt [1 2 3]))]))
   (for [c2 (range n-cities) c1 (range c2) :when  (util/rand-bool edge-p)]
     [(util/symbol-cat 'city c1) (util/symbol-cat 'city c2) (inc (rand-int max-gas))])
   'city0 (util/symbol-cat 'city (dec n-cities)) 0 max-gas))
   
   


(comment 

(def *e* (constant-predicate-simplify (make-discrete-road-trip-strips-env '{city3 2, city2 3, city1 1, city0 3} '([city0 city2 7] [city2 city1 5] [city3 city0 3]) 'city0 'city1 0 10)))

(defn test-rt 
  ([] (test-rt *road-trip*))
  ([env] 
     (doseq [f [#(get-hierarchy *drt-hierarchy* env) #(get-flat-strips-hierarchy env)]]
       (let [n (alt-node (f) icaps-choice-fn)]
	 (println (time (second (aha-star-search n))))))))

(interactive-search (alt-node (get-hierarchy *drt-hierarchy* ) (make-first-maximal-choice-fn '{act 10 next-stop1 9 next-stop2 9 next-stop3 9 fill-up1 8 fill-up2 8 fill-up3 8 drive-to 8})))


  (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1)

(let [e (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1)
        as (get-action-space e)]
    (map :name (applicable-actions (get-initial-state e) as)))

(map :name (first (a-star-graph-search (ss-node (make-road-trip-strips-env [['a 3 2] ['b 0 0] ['c 4 2]] '[[a b 2] [a c 1] [c b 1]] 'a 'b 0 4 1)))))
   

  (time (map :name (first (aha-star-search (alt-node (get-hierarchy *drt-hierarchy* (constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b 1 c nil d 3} '[[a b 30] [b c 40] [a c 60] [c d 20]] 'a 'd 0 64))) icaps-choice-fn)))))  
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
