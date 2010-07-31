(ns angelic.test.domains.warehouse
  (:use clojure.test
        angelic.domains.warehouse)
  (:require [angelic.env :as env]
            angelic.hierarchy.util
            [angelic.search.uniform-cost :as ucs]))



(def *warehouse-test-domains*
     [[[2 2 [2 2] false {1 '[a]} nil ['[a table2]]] -4]
      [[3 3 [2 2] false {1 '[a] 3 '[b]} nil ['[a b]]] -4]
      [[3 4 [2 3] false {1 '[b a] 3 '[c]} nil ['[a b c]]] -14]
      [[4 4 [2 3] false {1 '[a] 3 '[c b]} nil ['[a c table2]]] -50]
      [[4 4 [2 3] false {1 '[a] 3 '[c b]} nil ['[a c table1]]] -58]])

(deftest warehouse-ucs
  (doseq [[args reward] *warehouse-test-domains*]
    (is (= (->> args
                (apply make-warehouse-env)
                ucs/uniform-cost-search
                second)
           reward))))



(deftest warehouse-shop-ucs
  (doseq [[args reward] *warehouse-test-domains*
          h-fn [simple-warehouse-hierarchy simple-warehouse-hierarchy-fancynav]]
    (is (= (->> args
                (apply make-warehouse-env)
                h-fn
                angelic.hierarchy.util.ShopHTNEnv.
                ucs/uniform-cost-search
                second)
           reward))))


