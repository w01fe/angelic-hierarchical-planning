(ns angelic.test.domains.taxi-infinite
  (:use clojure.test
        angelic.domains.taxi-infinite)
  (:require [angelic.env :as env]
            angelic.hierarchy.util
            [angelic.search.uniform-cost :as ucs]))

(deftest infinite-taxi-random-env
  (is (= (:passengers (make-random-infinite-taxi-env 10 10 3 7))
         '([pass0 [1 5] [9 10]] [pass1 [1 5] [1 3]] [pass2 [9 2] [6 3]]))))


(def *infinite-taxi-test-domains*
     [[[3 3 3 0] -14]
      [[3 3 3 1] -8]])

(deftest infinite-taxi-ucs
  (doseq [[args reward] *infinite-taxi-test-domains*]
    (is (= (->> args
                (apply make-random-infinite-taxi-env)
                ucs/uniform-cost-search
                second)
           reward))))

(deftest infinite-taxi-ucs-sas
  (doseq [[args reward] *infinite-taxi-test-domains*
          env-fn [#_ make-random-infinite-taxi-sas make-random-infinite-taxi-sas2 make-random-infinite-taxi-sas3]]
    (is (= (->> args
                (apply env-fn)
                ucs/uniform-cost-search
                second)
           reward))))

(comment ;unfinished
 (deftest infinite-taxi-shop-ucs
   (doseq [[args reward] *infinite-taxi-test-domains*]
     (is (= (->> args
                 (apply make-random-infinite-taxi-env)
                 simple-infinite-taxi-hierarchy
                 hierarchy-util/make-shop-htn-env
                 ucs/uniform-cost-search
                 second)
            reward)))))
