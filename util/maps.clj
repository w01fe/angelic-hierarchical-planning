(in-ns 'angel.util)

(defn true-keys 
  "Return a lazy seq of the keys corresponding to logically true values in map."
  ([map] (for [[k v] map :when v] k))
  {:test (fn [] (is (= #{ 3 4 6} (set (true-keys {1 nil 2 false 3 true 4 'asfd 5 nil 6 1})))))})