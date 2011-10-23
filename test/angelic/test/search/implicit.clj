(ns angelic.test.search.implicit
  (:use clojure.test)
  (:require [angelic.env :as env]
            [angelic.domains.discrete-manipulation :as dm]
            [angelic.domains.nav-switch :as ns]
            [angelic.search.implicit
             [ah-astar :as aha]
             [sahtn :as sahtn]
             [dash-astar :as da]]))


(def *test-algorithms*
  [["sahtn" #(sahtn/sahtn % #{:nav :reach :discretem-tla 'top 'nav 'navh 'navv})]
   ["optimistic-ah-astar" #(aha/optimistic-ah-a* % true)]
   ["strict-ah-astar" #(aha/strict-ah-a* % true)]
   ["full-ah-astar" #(aha/full-ah-a* % true)]                          
   ["dash-astar" #(da/implicit-dash-a* %)]
   ["dash-astar-first" #(da/implicit-dash-a* % :choice-fn first)]
   ["dash-astar-ldfs" #(da/implicit-dash-a* % :search-strategy :ldfs)]
   ["dash-astar-hoc" #(da/implicit-dash-a* % :collect? :hierarchical)]
   ["dash-astar-nos" #(da/implicit-dash-a* % :abstract? false)]
   ["dash-astar-nods" #(da/implicit-dash-a* % :abstract? false :decompose? false)]])


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
  (doseq [[alg-name f] *test-algorithms*]
    (testing alg-name
      (doseq [[args reward] *discrete-manipulation-test-domains*]
        (is (= (-> (apply dm/make-discrete-manipulation-env-regions args)
                   dm/make-discrete-manipulation-hierarchy
                   alg
                   second)
               reward))))))

(def ^:private *nav-switch-test-domains*
     [[[10 [10 1] true  [1 10] #{[1 1]}] -37]
      [[10 [10 1] false [1 10] #{[1 1]}] -54]
      [[10 [10 1] true [1 10] #{[10 10]}] -54]
      [[10 [9 1] false [1 10] #{[1 1] [10 1]}] -42]])

(deftest hierarchical-nav-switch
  (doseq [[alg-name f]  all-variants]
    (testing alg-name
      (doseq [[args reward] *nav-switch-test-domains*]
        (is (= (-> (apply ns/make-nav-switch-env args)
                   (nav-switch/make-nav-switch-hierarchy true)
                   alg
                   second)
               reward))))))