(ns edu.berkeley.ai.domains.tests.test-nav-switch
 (:use clojure.test edu.berkeley.ai.domains.nav-switch 
       edu.berkeley.ai.search.algorithms.textbook 
       edu.berkeley.ai.search.state-space)
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.strips :as strips])
 )



(defn- get-and-check-sol [env]
  (map :name
    (first
     (envs/check-solution env
       (a-star-search 
	(make-initial-state-space-node 
	 env   
	 (constantly 0)))))))

(deftest flat-nav-switch
  (testing "non-strips"
    (is (= ['left 'flip 'down]
     (get-and-check-sol 
      (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1])))))
  (testing "strips"
    (is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))
    (is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/constant-predicate-simplify
       (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])))))
    (is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/flatten-strips-instance
       (strips/constant-predicate-simplify
	(make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))))))

