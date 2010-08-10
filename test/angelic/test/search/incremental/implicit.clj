(ns angelic.test.search.incremental.implicit
  (:use clojure.test
        angelic.search.incremental.implicit)
  (:import [angelic.search.incremental.implicit Status])
#_  (:require ))


(deftest dash-a*-status
  (let [s1 (Status. 0 :live)
        s2 (Status. 0 :blocked)
        s3 (Status. 0 :solved)
        s4 (Status. 1 :live)
        s5 (Status. 1 :blocked)
        s6 (Status. -1 :live)
        s7 (Status. -1 :solved)]
    (is (thrown? IllegalArgumentException (max-status s1 (Status. 0 nil))))
    (is (thrown? IllegalArgumentException (min-status s1 (Status. 0 :foo))))    
    (is (= s3 (max-status s1 s2 s3)))
    (is (= s4 (max-status s1 s2 s3 s4 s5 s6 s7)))
    (is (= best-status (max-status s1 s2 s3 s4 s5 s6 s7 best-status)))    
    (is (= s2 (min-status s1 s2 s3)))
    (is (= s6 (min-status s1 s2 s3 s4 s5 s6 s7)))
    (is (= worst-status (min-status s1 s2 s3 s4 s5 s6 s7 worst-status)))))




