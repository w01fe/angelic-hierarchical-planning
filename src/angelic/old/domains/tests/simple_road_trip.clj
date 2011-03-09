(ns angelic.old.domains.tests.simple-road-trip
 (:use clojure.test 
       angelic.old.domains.simple-road-trip
       )
 (:require [angelic.util :as util]  
           [angelic.old.search.algorithms.textbook :as algs]
           [angelic.old.search.state-space :as ss])
 )



(deftest simple-road-trip-test
  (let [args  '[ {a 3 b 3} [[a b 2]] a b 1]]
    (doseq [[e s] (map vector (map #(apply make-simple-road-trip-strips-env %) [args (conj args 1)]) [-299 -5])]
      (is (= s (second (algs/a-star-graph-search (ss/ss-node e)))))))
  (let [args  [ '{a 3 b 0 c 4} '[[a b 2] [a c 1] [c b 1]] 'a 'b 0 ]]
    (doseq [[e s] (map vector (map #(apply make-simple-road-trip-strips-env %) [args (conj args 1)]) [-302 -8])]
      (is (= s (second (algs/a-star-graph-search (ss/ss-node e))))))))

