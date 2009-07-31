(ns edu.berkeley.ai.domains.discrete-road-trip
 (:import [java.util HashSet])
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
	   [edu.berkeley.ai.util.graphs :as graphs]
           [edu.berkeley.ai.domains.strips :as strips]
	   [edu.berkeley.ai.angelic :as angelic]
	   [edu.berkeley.ai.angelic.dnf-valuations :as dv])
 )


; Note domination relation -- more gas is always better, given everything else.
; TODO: figure out how to take this into account?

(def *drt-hierarchy*               (util/path-local "discrete_road_trip.hierarchy"))
(def *drt-fancy-hierarchy*         (util/path-local "discrete_road_trip_fancy.hierarchy"))
(def *drt-flat-hierarchy*          (util/path-local "discrete_road_trip_flat.hierarchy"))
(def *drt-hierarchy-unguided*      (util/path-local "discrete_road_trip_unguided.hierarchy"))
(def *drt-fancy-hierarchy-unguided*(util/path-local "discrete_road_trip_fancy_unguided.hierarchy"))
(def *drt-flat-hierarchy-unguided* (util/path-local "discrete_road_trip_flat_unguided.hierarchy"))


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
  [city-gas-prices edges start dests max-gas]
  (println city-gas-prices edges start dests max-gas)
  (let [prices (map - (filter identity (distinct (vals city-gas-prices))))]
    (strips/make-strips-planning-instance 
     "discrete-road-trip"
     (make-discrete-road-trip-strips-domain)
     {'loc (keys city-gas-prices)
      'gas (range (inc max-gas))
      'price prices}  
     (set (concat 
	   [['at start] ['visited start] ['gas 0] ['max-gas max-gas] ['zero 0] ['one-greater max-gas max-gas]
	    ['max-price (apply min prices)] ['unpaid-gas 0]
	    ]
	   (for [[f t l] edges] ['road-length f t l])
	   (for [[l p] city-gas-prices] (if p ['gas-price l (- p)] ['no-gas l]))
	   (for [p1 prices, p2 prices] ['lower-price p1 p2 (max p1 p2)])
	   (for [x (range max-gas)] ['one-greater (inc x) x])
	   (for [x1 (range (inc max-gas)), x2 (range (inc max-gas))] ['overflow-sum x1 x2 (min (+ x1 x2) max-gas)])
	   (for [x1 (range (inc max-gas)), x2 (range (inc max-gas))] ['lower-gas x1 x2 (min x1 x2)])
	   (for [s (range (inc max-gas)), x (range (inc s))] ['sum x (- s x) s])
	   (for [x1 (range (inc max-gas)), x2 (range (inc x1))] ['geq x1 x2])
	   (medians 0 max-gas)))
     (for [d dests] ['visited d])
     (fn [s] 
       (format "At %s with %s gas." 
	       (some #(when (= (first %) 'at) (second %)) s)
	       (some #(when (= (first %) 'gas) (second %)) s)))
     )))

; Note; use of ICAPS choice fn is essential for good perf.

;(def *road-trip* (strips/constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b 1 c nil d 3} '[[a b 1] [b c 3] [c d 6]] 'a 'd 0 16)))

(defn make-random-drt-env [n-cities price-dist max-gas edge-p n-goals]
  (util/assert-is (> n-cities (inc n-goals)))
  (make-discrete-road-trip-strips-env
   (into {} (for [c (range n-cities)] [(util/symbol-cat 'city c) (util/sample-from price-dist)])) 
   (for [c1 (range n-cities) c2 (range n-cities) :when  (and (not (= c1 c2)) (util/rand-bool edge-p))]
     [(util/symbol-cat 'city c1) (util/symbol-cat 'city c2) (inc (rand-int max-gas))])
   'city0 (map #(util/symbol-cat 'city %) (range 1 (inc n-goals))) max-gas))

(defn make-random-dag-drt-env [n-cities price-dist max-gas edge-hl]
  (util/assert-is (> n-cities 1))
  (make-discrete-road-trip-strips-env
   (into {} (for [c (range n-cities)] [(util/symbol-cat 'city c) (util/sample-from price-dist)])) 
   (for [c2 (range n-cities) c1 (range c2) :when  (util/rand-bool (Math/pow 0.5 (double (/ (- c2 c1) edge-hl))))]
     [(util/symbol-cat 'city c1) (util/symbol-cat 'city c2) (inc (rand-int max-gas))])
   'city0 [(util/symbol-cat 'city (dec n-cities))] max-gas))
   
(defn make-random-tsp-drt-env [n-cities price-dist max-gas edge-p]
  (util/assert-is (> n-cities 1))
  (make-discrete-road-trip-strips-env
   (into {} (for [c (range n-cities)] [(util/symbol-cat 'city c) (util/sample-from price-dist)])) 
   (util/forcat [c1 (range n-cities) c2 (range c1) :when (and (util/rand-bool edge-p))]
     (let [sc1 (util/symbol-cat 'city c1), sc2 (util/symbol-cat 'city c2), g (inc (rand-int max-gas))]
       [[sc1 sc2 g] [sc2 sc1 g]]))
   'city0 (for [c (range n-cities)] (util/symbol-cat 'city c)) max-gas))
   


;; Heuristics

(def *drt-drive-cost* 5)

(derive ::DRTActDescriptionSchema ::angelic/PropositionalDescription)

(defmethod angelic/parse-description :drt-act [desc domain params]
  {:class ::DRTActDescriptionSchema})


(derive ::DRTActDescription ::angelic/PropositionalDescription)
(defstruct drt-act-description :class :fn :all-dnf)
(defn make-drt-act-description [fn all-dnf] (struct drt-act-description ::DRTActDescription fn all-dnf))




(defmethod angelic/instantiate-description-schema ::DRTActDescriptionSchema [desc instance]
  (let [goal-atoms   (util/safe-get instance :goal-atoms)
	const-preds  (util/safe-get instance :const-pred-map)
	road-lengths (util/safe-get const-preds 'road-length)
	gas-prices   (util/safe-get const-preds 'gas-price)
	cities       (util/to-set (util/safe-get-in instance [:trans-objects 'loc]))]
    (doseq [atom goal-atoms] (util/assert-is (= (first atom) 'visited)))
    (let [cheapest-gas (- (apply max (map #(nth % 2) gas-prices)))
	  goal-cities  (set (map second goal-atoms))
	  graph        (graphs/make-undirected-graph 
			cities
			(apply merge-with min (for [[_ c1 c2 l] road-lengths] {#{c1 c2} l})))
	  sp-graph     (graphs/shortest-path-graph graph)]
   ;   (println "CREATE ACT" cheapest-gas goal-cities sp-graph)
      (make-drt-act-description
       (fn [dnf]
	 (util/assert-is (= (count dnf) 1))
	 (let [visited   (HashSet.)
	       positions (HashSet.)
	       gas       (HashSet.)
	       unpaid    (HashSet.)]
	   (doseq [clause dnf, [atom] clause]
	     (let [pred (first atom)]
	       (cond (= pred 'visited) (.add visited   (nth atom 1))
		     (= pred 'at)      (.add positions (nth atom 1))
		     (= pred 'unpaid-gas)     (.add unpaid       (nth atom 1))
		     (= pred 'gas)     (.add gas       (nth atom 1)))))
	   (util/assert-is (= (count positions) 1))
	   (util/assert-is (= (count gas) 1))
	   (util/assert-is (= (count unpaid) 1))
	   (let [cities-of-interest (conj (apply disj goal-cities visited) (first positions))
		 sub-sp-graph       (graphs/sub-graph sp-graph cities-of-interest)
		 [mst dist]         (graphs/minimum-spanning-tree sub-sp-graph)]
	     (- 0 
		(* dist *drt-drive-cost*)
		(* cheapest-gas (max 0 (- dist (- (first gas) (first unpaid)))))))))
       (into {} (map #(vector % :unknown) (util/safe-get instance :all-atoms)))
))))
	  

(defmethod angelic/ground-description ::DRTActDescription [desc var-map] desc)
  

(defmethod angelic/progress-valuation [::angelic/PessimalValuation ::DRTActDescription] [val desc]  val)

(defmethod angelic/progress-valuation [::dv/DNFValuation ::DRTActDescription] [val desc]
  (angelic/make-conditional-valuation 
   envs/*true-condition*
   (+ (angelic/valuation-max-reward val) 
      ((:fn desc) (keys (util/safe-get val :clause-map))))))

(defmethod angelic/progress-clause ::DRTActDescription [clause desc]
  [[(with-meta 
     (:all-dnf desc)
     {:pre-clause clause})
    ((:fn desc) [clause])]])

(defmethod angelic/regress-clause-state ::DRTActDescription [state pre-clause desc post-clause-pair]
  (if-let [[post-clause step-rew] post-clause-pair]
      [(angelic/minimal-clause-state pre-clause) step-rew]
    [(angelic/minimal-clause-state pre-clause)
     ((:fn desc) [pre-clause])]))












(comment 


(defn test-rot 
  ([env] 
     (doseq [i (range 2), f [#(get-hierarchy *drt-hierarchy* env) #(get-flat-strips-hierarchy env) #(get-hierarchy *drt-flat-hierarchy* env)]]
       (let [n (alt-node (f) icaps-choice-fn)]
	 (println (time (second (aha-star-search n))))))))

(defn test-rot 
  ([env] 
     (doseq [i (range 2), [f t] [[#(get-hierarchy *drt-hierarchy* env) true] [#(get-hierarchy *drt-flat-hierarchy* env) false]]]
       (let [n (alt-node (f) icaps-choice-fn) sol (time (aha-star-search n))]
	 (if t (println (map :name (first sol)))) (println (second sol))))))

(do (def *e* (constant-predicate-simplify (make-random-discrete-road-trip-strips-env 3 '{nil 0.3, 1 0.2, 2 0.5}  63 0.5))) (time-limit (test-rot *e*) 10))

(do (def *e* (constant-predicate-simplify (make-random-dag-drt-env 5 '{nil 0.3, 1 0.2, 10 0.5} 63 3))) (test-rot *e*))

(do (def *e* (constant-predicate-simplify (make-random-drt-tsp 5 '{nil 0.3, 1 0.2, 10 0.5} 63 1.0))) (test-rot *e*))


; with subsumption!

(defn test-rot 
  ([env] 
     (doseq [subs [{} {'gas >= 'unpaid-gas <=}], [f t] [[#(get-hierarchy *drt-hierarchy* env) true] [#(get-hierarchy *drt-fancy-hierarchy* env) false] [#(get-hierarchy *drt-flat-hierarchy* env) false]]]
       (let [n (alt-node (f) subs icaps-choice-fn true true) sol (time (aha-star-search n))]
	 (println (sref-get *ref-counter*)) (reset-ref-counter) (if t (println (map :name (first sol)))) (println (second sol))))))

(map :name (first (aha-star-search (alt-node (get-hierarchy *drt-hierarchy* (constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 4 b 2 c 3 d 1} '[[a b 10] [a c 10] [b d 5] [c d 5]] 'a '[d] 15))) '{gas >} icaps-choice-fn true true))))

(interactive-search (alt-node (get-hierarchy *drt-hierarchy* ) (make-first-maximal-choice-fn '{act 10 next-stop1 9 next-stop2 9 next-stop3 9 fill-up1 8 fill-up2 8 fill-up3 8 drive-to 8})))


  (constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b nil} '[[a b 5]] 'a '[b] 10))

(let [e (make-road-trip-strips-env [['a 3 2] ['b 0 0]] '[[a b 2]] 'a 'b 1 4 1)
        as (get-action-space e)]
    (map :name (applicable-actions (get-initial-state e) as)))
   

  (time (map :name (first (aha-star-search (alt-node (get-hierarchy *drt-hierarchy* (constant-predicate-simplify (make-discrete-road-trip-strips-env '{a 2 b 1 c nil d 3} '[[a b 30] [b c 40] [a c 60] [c d 20]] 'a 'd 0 64))) icaps-choice-fn)))))  
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
