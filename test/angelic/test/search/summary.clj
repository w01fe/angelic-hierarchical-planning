(ns angelic.test.search.summary
  (:use clojure.test)
  (:require [angelic.search.summary :as summary]))

(defn sge [x y] (summary/>= x y Double/POSITIVE_INFINITY))

(def +best-simple-summary+ (summary/make-solved-simple-summary Double/POSITIVE_INFINITY :best))

(defn smax [& stats] (summary/apply-max-b stats 10000))

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
    (is (= s3 (smax s1 s2 s3)))
    (is (= s4 (smax s1 s2 s3 s4 s5 s6 s7)))
    (is (= +best-simple-summary+
           (smax s1 s2 s3 s4 s5 s6 s7 +best-simple-summary+)))    

    (is (= (contents (summary/+ s4 s5 :d Double/POSITIVE_INFINITY)) [2 :live]))
    (is (= (contents (summary/+ s4 s3 :d Double/POSITIVE_INFINITY)) [1 :blocked]))    
    (is (= (contents (summary/+ s2 s5 :d Double/POSITIVE_INFINITY)) [1 :live]))
    (is (= (contents (summary/+ s7 s3 :d Double/POSITIVE_INFINITY)) [-1 :solved]))))





