(ns edu.berkeley.ai.domains.warehouse
 (:use clojure.test 
       edu.berkeley.ai.domains.warehouse
       edu.berkeley.ai.search.algorithms.textbook
       edu.berkeley.ai.search.state-space
       )
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.strips :as strips]
	   [edu.berkeley.ai.angelic :as angelic]
	   [edu.berkeley.ai.angelic.dnf-valuations :as dv])
 )







(defn- get-and-check-sol [env graph?]
  (map :name
    (first
     (envs/check-solution env
       ((if graph? 
	  a-star-graph-search 
	  a-star-search)
	(make-initial-state-space-node 
	 env   
	 (constantly 0)))))))

(deftest flat-warehouse
  (testing "tiny instance"
    (let [env (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])]
      (doseq [graph? [true false]
	      simplifier [identity strips/constant-predicate-simplify
			  (comp strips/flatten-strips-instance strips/constant-predicate-simplify)]]
	(is (= '((get-l a table0 x0 x1 y1) (left x1 x0 y1) (turn-r x0 y1) (put-r a table1 x1 x0 y0 y1))
		    (get-and-check-sol (simplifier env) graph?))))))
  (testing "bigger instance"
    (let [env (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]])]
      (doseq [simplifier [strips/constant-predicate-simplify
			  (comp strips/flatten-strips-instance strips/constant-predicate-simplify)]]
	(is (= 14 
		    (count (get-and-check-sol (simplifier env) true))))))))


(comment

(defn find-goal-states [env]
  (let [goal   (envs/get-goal env)
	as     (envs/get-action-space env)
	states (HashSet.)]
    (loop [open [(envs/get-initial-state env)]
	   goals []]
      (if (empty? open) goals
	  (let [state (first open)]
	    (if (.contains states state)
	        (recur (next open) goals)
	      (do (.add states state)
	        (if (envs/satisfies-condition? state goal)
		    (recur (next open) (conj goals state))
		  (recur (concat (envs/successor-states state as) (next open)) goals)))))))))

    
(defn test-descriptions 
  ([env max-tests]
     (test-descriptions env (find-goal-states env) max-tests))
  ([env goal-states max-tests]
  (let [desc (angelic/ground-description
	      (angelic/instantiate-description-schema
	       (angelic/parse-description [:warehouse-act] (make-warehouse-strips-domain) nil)
	       env)
	      nil)
	as (envs/get-action-space env)
	done (HashSet.)]
    (doseq [s goal-states] (.add done s))
    (loop [gen (distinct goal-states), rew 0, max-tests max-tests]
      (println "Generation" rew "has" (count gen) "states...")
      (doseq [s (take max-tests gen)]
	(let [val (angelic/state->valuation :edu.berkeley.ai.angelic.dnf-valuations/DNFValuation s)] 
	  (util/assert-is (>= (angelic/valuation-max-reward (angelic/progress-valuation val desc)) rew))))
      (when (and (not (empty? gen)) (> max-tests (count gen)))
	(recur 
	 (for [s gen, ss (envs/successor-states s as) :when (not (.contains done ss))] 
	   (do (.add done ss) ss))
	 (dec rew)
	 (- max-tests (count gen)))))))))

; (test-descriptions (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]])) (for [bpos [0 2 3], [gpos fr] [[[0 2] true] [[2 2] false]]] (get-initial-state (constant-predicate-simplify (make-warehouse-strips-env 4 4 gpos fr {bpos '[b] 1 '[a c]} nil ['[table1 table0]])))) 10)

; (test-descriptions (constant-predicate-simplify (make-warehouse-strips-env 7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]])) (for [[gpos fr] [[[4 4] true] [[6 4] false]]] (get-initial-state (constant-predicate-simplify (make-warehouse-strips-env 7 6 gpos fr {5 '[a b c]} nil ['[a b c table5]])))) 100000)
 ;)




