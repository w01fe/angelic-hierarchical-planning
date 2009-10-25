(ns edu.berkeley.ai.angelic.hybrid.tests.strips-hierarchies
  (:use clojure.test)
  (:require [edu.berkeley.ai.domains.hybrid-blocks :as hb]
            [edu.berkeley.ai.angelic.hierarchies :as hierarchies]
            [edu.berkeley.ai.angelic.algorithms 
             [abstract-lookahead-trees :as alts]
             [offline :as offline]]
            [edu.berkeley.ai.angelic.hybrid [solutions :as sol]]
            ))

(deftest hybrid-strips-hierarchies
  (let [e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])
        [sol rew] (offline/aha-star-search 
                   (alts/alt-node 
                    (hierarchies/get-hierarchy hb/*hybrid-blocks-hierarchy* e) 
                    {:cache? false :graph? false}))]
    (is (= (map :name (sol/extract-hybrid-primitive-solution e sol))
           '([up-empty 1] [right-empty 5] [down-empty 1] [get b table] 
               [up-holding b 2] [left-holding b 2] [down-holding b 2] [put b a])))
    (is (= rew -20))))








