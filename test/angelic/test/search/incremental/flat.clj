(ns angelic.test.search.incremental.flat
  (:use clojure.test
        angelic.domains.nav-switch)
  (:require [angelic.env :as env]
            [angelic.hierarchy.util :as hierarchy-util]
            [angelic.search.incremental.flat :as ucs]))


(def ^:private *nav-switch-test-domains*
     [[[10 [10 1] true  [1 10] #{[1 1]}] -37]
      [[10 [10 1] false [1 10] #{[1 1]}] -54]
      [[10 [10 1] true [1 10] #{[10 10]}] -54]
      [[10 [9 1] false [1 10] #{[1 1] [10 1]}] -42]
      [[20 [20 1] true [1 20]  #{[7 6] [8 7] [11 10] [13 12] [11 11] [12 13] [17 18] [2 4] [13 15]
                                 [18 20] [1 3] [17 20] [2 7] [13 18] [3 9] [5 12] [7 14] [9 16] [10 17]
                                 [7 16] [10 19] [4 14] [5 15] [6 16] [2 15] [7 20] [20 2] [1 16] [20 4]
                                 [16 3] [20 7] [14 2] [15 4] [20 10] [16 7] [11 3] [18 10] [19 11] [9 3]
                                 [14 8] [6 1] [10 5] [19 14] [7 3] [11 7] [12 8] [6 3] [8 5] [18 15] [19 16]}]
        -79]])

(deftest incremental-ucs-nav-switch
  (doseq [[args reward] *nav-switch-test-domains*]
    (is (= (->> args
                (apply make-nav-switch-env)
                ucs/uniform-cost-search
                second)
           reward))))


