(ns angelic.test.domains.taxi
  (:use clojure.test
        angelic.domains.taxi)
  (:require [angelic.env :as env]
            [angelic.hierarchy.util :as hierarchy-util]
            [angelic.search.textbook :as ucs]))

(deftest taxi-random-env
  (is (= (:passengers (make-random-taxi-env 10 10 3 7))
         '([pass0 [1 5] [9 10]] [pass1 [1 5] [1 3]] [pass2 [9 2] [6 3]]))))


(def *taxi-test-domains*
     [[[5 5 5 0] -40]
      [[5 5 5 1] -33]])

(deftest taxi-ucs
  (doseq [[args reward] *taxi-test-domains*]
    (is (= (->> args
                (apply make-random-taxi-env)
                ucs/uniform-cost-search
                second)
           reward))))

(deftest taxi-ucs-sas
  (doseq [[args reward] *taxi-test-domains*
          env-fn [make-random-taxi-sas make-random-taxi-sas2]]
    (is (= (->> args
                (apply env-fn)
                ucs/uniform-cost-search
                second)
           reward))))

(deftest taxi-shop-ucs
  (doseq [[args reward] *taxi-test-domains*
          h-fn [simple-taxi-hierarchy simple-taxi-hierarchy2 simple-taxi-hierarchy3]]
    (is (= (->> args
                (apply make-random-taxi-env)
                h-fn
                hierarchy-util/make-shop-htn-env
                ucs/uniform-cost-search
                second)
           reward))))



;; TODO: test descriptions