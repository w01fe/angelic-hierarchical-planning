(ns angelic.test.domains.discrete-manipulation
  (:use clojure.test
        angelic.domains.discrete-manipulation)
  (:require [angelic.env :as env]
            [angelic.hierarchy.util :as hierarchy-util]
            [angelic.search.uniform-cost :as ucs]))


(deftest discrete-manipulation-print
  (is (= (state-str
          (env/initial-state
           (make-discrete-manipulation-env [10 10] [2 1] [ [ [4 4] [6 6] ] ] [ [:a [4 5] #{ [4 4] } ] ] 2)))
"***********
* B       *
*         *
*         *
*   ...   *
*   a..   *
*   ...   *
*         *
*         *
*         *
***********
parked
")))

(deftest discrete-manipulation-regions-sampling
  (let [e (make-discrete-manipulation-env-regions
           [10 10] [1 1] [[[4 4] [6 6]]]
           [[:a [5 5] [[4 4] [6 6]]] [:b [4 5] [[5 5] [6 6]]]]
           2 2 2)
        const (:const (:init e))]
    (is (= (const [:base-offsets])
           '([-3 0] [0 -2] [1 1] [3 0] [0 1] [0 3] [-1 1] [2 0] [1 2] [0 -3] [0 -1] [1 0] [0 0]
               [0 2] [2 1] [1 -1] [-2 0] [-1 -2] [-1 2] [1 -2] [-2 1] [2 -1] [-2 -1] [-1 0] [-1 -1])))
    (is (= (const [:goal :a])  #{[5 4] [4 4]}))
    (is (= (const [:goal :b])  #{[5 5] [6 6]}))))

(deftest discrete-manipulation-random-env
  (is (= (get-in (make-random-discrete-manipulation-env 6 3) [:init :const [:objects] ])
         [[:a [15 13] #{[4 6] [6 3]}] [:b [4 3] #{[14 13] [16 14]}] [:c [13 5] #{[6 13] [4 13]}] [:d [15 6] #{[3 13] [3 16]}] [:e [15 3] #{[4 3] [3 6]}] [:f [16 15] #{[13 3] [14 6]}]])))


(def *discrete-manipulation-test-domains*
     [[[[10 10] [1 1] [[[4 4] [6 6]]]
        [[:a [5 5] [[4 4] [6 6]]] [:b [4 5] [[5 5] [6 6]]]] 2 2 2]
       -27 -29]
      [[[10 5] [9 4] [[[2 2] [3 3]] [[4 1] [4 1]] [[5 2] [7 3]]]
        [[:a [2 3] [[5 2] [7 3]]] [:b [7 3] [[4 1] [4 1]]] [:c [4 1] [[2 2] [3 3]]]] 1 1 1]
       -61 -133]
      [[[10 5] [9 4] [[[2 2] [3 3]] [[4 1] [4 1]] [[5 2] [7 3]]]
        [[:a [2 3] [[5 2] [7 3]]] [:b [7 3] [[4 1] [4 1]]] [:c [4 1] [[2 2] [3 3]]]] 2 1 1]
       -37 -68]
      [[[10 5] [9 4] [[[2 2] [3 3]] [[4 1] [4 1]] [[5 2] [7 3]]]
        [[:a [2 3] [[7 3] [7 3]]] [:b [7 3] [[4 1] [4 1]]] [:c [4 1] [[2 3] [2 3]]]] 1 1 1]
       nil nil]])

(deftest discrete-manipulation-ucs
  (doseq [[args reward _] *discrete-manipulation-test-domains*]
    (is (= (->> args
                (apply make-discrete-manipulation-env-regions)
                ucs/uniform-cost-search
                second)
           reward))))

(deftest discrete-manipulation-shop-ucs
  (doseq [[args _ reward] *discrete-manipulation-test-domains*]
    (is (= (->> args
                (apply make-discrete-manipulation-env-regions)
                make-discrete-manipulation-hierarchy
                hierarchy-util/make-shop-htn-env
                ucs/uniform-cost-search
                second)
           reward))))






;; TODO: test descriptions