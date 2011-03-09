(ns angelic.old.angelic.algorithms.tests.abstract-lookahead-trees
  (:use clojure.test angelic.old.angelic angelic.old.angelic.hierarchies
	angelic.old.angelic.algorithms.abstract-lookahead-trees)
  (:import [java.util HashMap Map$Entry HashSet])
  (:require [angelic.util :as util] [angelic.old  [envs :as envs] [search :as search]]
	    [angelic.util.graphs :as graphs]
		[angelic.old.envs.strips :as strips]
	    [angelic.old.domains 
	     [nav-switch :as nav-switch]
	     [warehouse :as warehouse]]
	    [angelic.old.angelic.hierarchies.strips :as strips-hierarchies]
	    [angelic.old.search.algorithms.textbook :as textbook]
	    [angelic.old.angelic.hierarchies.flat :as flat]
	    ))









;; Tests and other miscellanea


	    



(defn- get-and-check-sol [sol initial-plan]
  (doseq [cache? [true false]
	  graph? [true false]]
    ;(println cache? graph?)
    (is (contains? sol 
      (map :name
         (first
	  (envs/check-solution (hla-environment (first initial-plan))
	    (angelic.old.search.algorithms.textbook/a-star-search
	    (alt-node initial-plan {:cache? cache? :graph? graph?})))))))))


(def *flat-ns* (nav-switch/make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *flat-ns-sol* #{['left 'flip 'down]})

(def *strips-ns* (nav-switch/make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))
(def *strips-ns-sol* #{'[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]})

(def *flat-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) 1))))))
(def *strips-ns-heur* (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) 1))))))

(def *simplifiers* [identity 
		     strips/constant-predicate-simplify
		     (comp strips/flatten-strips-instance strips/constant-predicate-simplify)])

(deftest alt-nav-switch
   (testing "flat hierarchy, non-strips"
     (get-and-check-sol *flat-ns-sol* (flat/get-flat-hierarchy *flat-ns*))
     (get-and-check-sol *flat-ns-sol* (flat/get-flat-hierarchy *flat-ns* *flat-ns-heur*)))
   (testing "flat hierarchy, strips"
     (get-and-check-sol *strips-ns-sol* (flat/get-flat-hierarchy *strips-ns* *strips-ns-heur*))
     (doseq [simplifier *simplifiers*]
       (get-and-check-sol *strips-ns-sol* (flat/get-flat-hierarchy (simplifier *strips-ns*)))))
   (testing "flat-strips hierarchy"
     (get-and-check-sol *strips-ns-sol* (strips-hierarchies/get-flat-strips-hierarchy *strips-ns* *strips-ns-heur*))
     (doseq [simplifier (butlast *simplifiers*)]
       (get-and-check-sol *strips-ns-sol* (strips-hierarchies/get-flat-strips-hierarchy (simplifier *strips-ns*)))))
   (testing "Ordinary strips hierarchy"
     (doseq [simplifier (butlast *simplifiers*)]
    ;   (println simplifier)
       (get-and-check-sol *strips-ns-sol* (get-hierarchy nav-switch/*nav-switch-hierarchy* (simplifier *strips-ns*))))))		

(def *strips-wh* (warehouse/make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))
(def *strips-wh-sols* 
  #{'((get-l a table0 x0 x1 y1) (left x1 x0 y1) (turn-r x0 y1) (put-r a table1 x1 x0 y0 y1))
	 '((get-l a table0 x0 x1 y1) (turn-r x1 y1) (left x1 x0 y1) (put-r a table1 x1 x0 y0 y1))}) 			      






(deftest alt-down-warehouse
 (testing "flat-strips hierarchy"
   (doseq [simplifier [(second *simplifiers*)]
	   maker [strips-hierarchies/get-flat-strips-hierarchy 
		  #(get-hierarchy warehouse/*warehouse-hierarchy-unguided* %)]]
     (get-and-check-sol *strips-wh-sols* (maker (simplifier *strips-wh*))))))
