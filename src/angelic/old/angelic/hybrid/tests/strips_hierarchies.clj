(ns angelic.old.angelic.hybrid.tests.strips-hierarchies
  (:use clojure.test)
  (:require [angelic.old.domains.hybrid-blocks :as hb]
            [angelic.old.domains.simple-road-trip :as srt]
            [angelic.old.angelic.hierarchies :as hierarchies]
            [angelic.old.search.algorithms.textbook :as textbook]
            [angelic.old.angelic.algorithms 
             [abstract-lookahead-trees :as alts]]
            [angelic.old.angelic.hybrid [solutions :as sol]]
            ))

(deftest hybrid-strips-hierarchies
  (let [e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])
        [sol rew] (textbook/a-star-search 
                   (alts/alt-node 
                    (hierarchies/get-hierarchy hb/*hybrid-blocks-hierarchy-unguided* e) 
                    {:cache? false :graph? false :ref-choice-fn alts/first-choice-fn}))]
    (is (= (map :name (sol/extract-hybrid-primitive-solution e sol))
           '([up-empty 1] [right-empty 5] [down-empty 1] [get b table] 
               [up-holding b 2] [left-holding b 2] [down-holding b 2] [put b a])))
    (is (= rew -14))))

(deftest simple-road-trip
  (let [e (srt/make-simple-road-trip-strips-env '{a 5 b 0 c 2} '[[a b 3] [a c 1] [c b 3]] 'a 'b 0) 
        [s r] (textbook/a-star-search 
               (alts/alt-node (hierarchies/get-hierarchy srt/*simple-road-trip-hierarchy* e) 
                         {:cache? false :graph? false :ref-choice-fn alts/first-choice-fn}))]
    (is (= r -15))
    (is (= (map :name (sol/extract-hybrid-primitive-solution e s))
           '([refuel a 1] [drive a c] [refuel c 3] [drive c b]))))
  (let [e (srt/make-simple-road-trip-strips-env '{a 5 b 0 c 20 z 10} 
                                                '[[a z 100] [z b 30] [a c 90] [c b 20]] 'a 'b 0) 
        [s r] (textbook/a-star-search 
               (alts/alt-node (hierarchies/get-hierarchy srt/*simple-road-trip-hierarchy* e) 
                         {:cache? false :graph? false :ref-choice-fn alts/first-choice-fn}))]
    (is (= r -810))
    (is (= (map :name (sol/extract-hybrid-primitive-solution e s))
           '([refuel a 100] [drive a c] [refuel c 10] [drive c b]))))
  )






