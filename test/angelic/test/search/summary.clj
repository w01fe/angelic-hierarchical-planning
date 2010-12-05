(ns angelic.test.search.summary
  (:use clojure.test)
  (:require [angelic.search.summary :as summary]))

(defn contents [s]
  ((juxt summary/max-reward summary/status) s))

(deftest summary
  (let [s1 (summary/make-blocked-simple-summary 0 nil)
        s2 (summary/make-live-simple-summary 0 nil)
        s3 (summary/make-solved-simple-summary 0 nil)
        s4 (summary/make-blocked-simple-summary 1 nil)
        s5 (summary/make-live-simple-summary 1 nil)
        s6 (summary/make-blocked-simple-summary -1 nil)
        s7 (summary/make-solved-simple-summary -1 nil)]
    (is (= s3 (summary/max s1 s2 s3)))
    (is (= s4 (summary/max s1 s2 s3 s4 s5 s6 s7)))
    (is (= summary/+best-simple-summary+
           (summary/max s1 s2 s3 s4 s5 s6 s7 summary/+best-simple-summary+)))    
    (is (= s2 (summary/min s1 s2 s3)))
    (is (= s6 (summary/min s1 s2 s3 s4 s5 s6 s7)))
    (is (= summary/+worst-simple-summary+
           (summary/min s1 s2 s3 s4 s5 s6 s7 summary/+worst-simple-summary+)))
    (doseq [s [s1 s2 s3 s4 s5 s6 s7]]
      (is (= (contents (summary/+ s summary/+zero-simple-summary+)) (contents s)))
      (is (= (contents (summary/+ summary/+zero-simple-summary+ s)) (contents s))))

    (is (= (contents (summary/+ s4 s5)) [2 :live]))
    (is (= (contents (summary/+ s4 s3)) [1 :blocked]))    
    (is (= (contents (summary/+ s2 s5)) [1 :live]))
    (is (= (contents (summary/+ s7 s3)) [-1 :solved]))))





