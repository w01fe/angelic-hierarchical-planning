(ns angelic.test.search.incremental.hierarchical
  (:use clojure.test
        angelic.search.incremental.hierarchical)
  (:require [angelic.env :as env]
            [angelic.domains.discrete-manipulation :as discrete-manipulation]
            [angelic.domains.nav-switch :as nav-switch]))



(def ^:private *discrete-manipulation-test-domains*
     [[[[10 10] [1 1] [[[4 4] [6 6]]]
        [[:a [5 5] [[4 4] [6 6]]] [:b [4 5] [[5 5] [6 6]]]] 2 2 2]
       -29]
      [[[10 5] [9 4] [[[2 2] [3 3]] [[4 1] [4 1]] [[5 2] [7 3]]]
        [[:a [2 3] [[5 2] [7 3]]] [:b [7 3] [[4 1] [4 1]]] [:c [4 1] [[2 2] [3 3]]]] 1 1 1]
       -133]
      [[[10 5] [9 4] [[[2 2] [3 3]] [[4 1] [4 1]] [[5 2] [7 3]]]
        [[:a [2 3] [[5 2] [7 3]]] [:b [7 3] [[4 1] [4 1]]] [:c [4 1] [[2 2] [3 3]]]] 2 1 1]
       -68]])



(deftest hierarchical-discrete-manipulation
  (doseq [ [alg-name alg]  all-algorithms]
    (testing alg-name
      (doseq [[args reward _] *discrete-manipulation-test-domains*]
        (is (= (->> args
                    (apply discrete-manipulation/make-discrete-manipulation-env-regions)
                    discrete-manipulation/make-discrete-manipulation-hierarchy
                    alg
                    second)
               reward))))))

(def ^:private *nav-switch-test-domains*
     [[[10 [10 1] true  [1 10] #{[1 1]}] -37]
      [[10 [10 1] false [1 10] #{[1 1]}] -54]
      [[10 [10 1] true [1 10] #{[10 10]}] -54]
      [[10 [9 1] false [1 10] #{[1 1] [10 1]}] -42]])

(deftest hierarchical-nav-switch
  (doseq [ [alg-name alg]  all-algorithms]
    (testing alg-name
      (doseq [[args reward _] *nav-switch-test-domains*]
        (is (= (->> args
                    (apply nav-switch/make-nav-switch-env)
                    (#(nav-switch/make-nav-switch-hierarchy % true))
                    alg
                    second)
               reward))))))