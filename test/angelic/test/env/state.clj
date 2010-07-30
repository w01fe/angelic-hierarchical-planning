(ns angelic.test.env.state
	(:require [edu.berkeley.ai.util :as util])
	(:use clojure.test 
		  angelic.env.state))

(deftest test-logging-factored-state
  (let [si {:a 1 :b 2 :c 3}
        s1 (get-logger si #{:a})
        s2 (set-var s1 :a 1)
        s3 (set-var s1 :b 2)
        s4 (set-var (set-var s1 :a 1) :b 2)
        s5 (set-var (set-var s1 :a 1) :c 4)
        ss [s1 s2 s3 s4 s5]
        equal-sets [#{0 1} #{2 3} #{4}]
        ]
    (is (= (map as-map          ss) [si si si si (assoc si :c 4)]))
    (is (= (map extract-effects ss) [{} {:a 1} {:b 2} {:a 1 :b 2} {:a 1 :c 4}]))
    (is (= (map ooc-effects     ss) [{} {} {:b 2} {:b 2} {:c 4}]))
    (doseq [es equal-sets] 
      (is (apply = (map ss es)))
      (is (apply = (map (comp hash ss) es))))
    (doseq [[s1 s2] (util/combinations equal-sets 2), i1 s1, i2 s2]
      (is (not (= i1 i2)))
      (is (not (= (hash i1) (hash i2)))))))


