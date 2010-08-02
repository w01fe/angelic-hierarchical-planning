(ns angelic.test.hierarchy.state-set
  (:refer-clojure :exclude [empty?])
  (:use clojure.test
        angelic.hierarchy.state-set)  
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env.state :as state]))


(deftest test-logging-factored-state-set-singletons
  (let [bare {:a 1 :b 2 :c 3}
        si (make-singleton-logging-factored-state-set bare)
        s1 (state/get-logger si #{:a})
        s2 (state/set-var s1 :a #{1})
        s3 (state/set-var s1 :b #{2})
        s4 (state/set-var (state/set-var s1 :a #{1}) :b #{2})
        s5 (state/set-var (state/set-var s1 :a #{1}) :c #{4})
        ss [s1 s2 s3 s4 s5]
        equal-sets [#{0 1} #{2 3} #{4}]]
    (is (= (map singleton          ss) [bare bare bare bare (assoc bare :c 4)]))
    (is (= (map state/extract-effects ss) [{} {:a #{1}} {:b #{2}} {:a #{1} :b #{2}} {:a #{1} :c #{4}}]))
    (is (= (map state/ooc-effects     ss) [{} {} {:b #{2}} {:b #{2}} {:c #{4}}]))
    (doseq [es equal-sets] 
      (is (apply = (map ss es)))
      (is (apply = (map (comp hash ss) es))))
    (doseq [[s1 s2] (util/combinations equal-sets 2), i1 s1, i2 s2]
      (is (not (= i1 i2)))
      (is (not (= (hash i1) (hash i2)))))))

(deftest logging-factored-state-set-sets
  (let [bare {:a 1 :b 2 :c 3 :d 4}
        si   (make-singleton-logging-factored-state-set bare)
        s1   (state/get-logger si #{:a :b})
        s2   (state/set-var s1 :a #{2 3 4})
        s3   (constrain s2 {:a #{3 4 5} :b #{2}})
        s4   (state/set-var s3 :c #{7})
        s5   (state/set-var s4 :a #{8})]
    (is (empty? (state/set-var s5 :a #{})))
    (is (not-any? empty? [s1 s2 s3 s4 s5]))
    (is (= (singleton s5) {:a 8 :b 2 :c 7 :d 4}))
    (is (not-any? singleton [s2 s3 s4]))
    (is (thrown? AssertionError (constrain s1 {:c #{5}})))
    (is (empty? (constrain s3 {:a #{5}})))
    (is (= (explicit-set (state/set-var s3 :c #{4 5}))
           #{{:a 3 :b 2 :c 4 :d 4} {:a 4 :b 2 :c 4 :d 4}
             {:a 3 :b 2 :c 5 :d 4} {:a 4 :b 2 :c 5 :d 4}}))
    (is (= (state/extract-effects s4) {:a #{3 4} :b #{2} :c #{7}}))
    (is (= (state/ooc-effects s4) {:c #{7}}))
    (= (explicit-set (state/transfer-effects
                      (make-singleton-logging-factored-state-set {:a 6 :b 5 :c 4 :d 3})
                      s4))
       #{{:a 3 :b 2 :c 7 :d 3} {:a 4 :b 2 :c 7 :d 3}})))



