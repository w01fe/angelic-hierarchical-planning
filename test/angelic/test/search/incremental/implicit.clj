(ns angelic.test.search.incremental.implicit
  (:use clojure.test
        angelic.search.incremental.implicit)
  (:import [angelic.search.incremental.implicit Status])
#_  (:require ))


(deftest dash-a*-status
  (let [s1 (Status. 0 :blocked)
        s2 (Status. 0 :live)
        s3 (Status. 0 :solved)
        s4 (Status. 1 :blocked)
        s5 (Status. 1 :live)
        s6 (Status. -1 :blocked)
        s7 (Status. -1 :solved)]
    (is (thrown? IllegalArgumentException (max-status s1 (Status. 0 nil))))
    (is (thrown? IllegalArgumentException (min-status s1 (Status. 0 :foo))))    
    (is (= s3 (max-status s1 s2 s3)))
    (is (= s4 (max-status s1 s2 s3 s4 s5 s6 s7)))
    (is (= +best-status+ (max-status s1 s2 s3 s4 s5 s6 s7 +best-status+)))    
    (is (= s2 (min-status s1 s2 s3)))
    (is (= s6 (min-status s1 s2 s3 s4 s5 s6 s7)))
    (is (= +worst-status+ (min-status s1 s2 s3 s4 s5 s6 s7 +worst-status+)))
    (doseq [s [s1 s2 s3 s4 s5 s6 s7]]
      (is (= (add-statuses s zero-status) s))
      (is (= (add-statuses zero-status s) s)))

    (is (= (add-statuses s4 s5) (Status. 2 :live)))
    (is (= (add-statuses s4 s3) (Status. 1 :blocked)))    
    (is (= (add-statuses s2 s5) (Status. 1 :live)))
    (is (= (add-statuses s7 s3) (Status. -1 :solved)))))





