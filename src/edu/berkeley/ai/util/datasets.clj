(ns edu.berkeley.ai.util.datasets
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.charts)
  )

(defmacro ds-fn [bindings & body]
  (let [ds (gensym)]
    `(fn [~ds]
       (let ~(vec (interleave bindings (map (fn [b] `(safe-get ~ds ~(keyword (name b)))) bindings)))
	 ~@body))))

(defn ds->chart [ds group-fields x y]
  (struct-map chart :key "on" :series 
    (for [[k v] (group-by (fn [d] (vec (map #(safe-get d %) group-fields))) ds)]
      (struct-map series :title k 
		 :data (sort-by first (map (fn [d] [(safe-get d x) (safe-get d y)]) v))))))

	    