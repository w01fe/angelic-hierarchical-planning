(ns edu.berkeley.ai.util.datasets
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.charts)
  )

; Data set is just a list of maps with the same keys.

(defmacro ds-fn [bindings & body]
  (let [ds (gensym)]
    `(fn [~ds]
       (let ~(vec (mapcat #(if (vector? %) 
			       [(first %) `(get ~ds ~(keyword (name (first %))) ~(second %))]
			     [% `(safe-get ~ds ~(keyword (name %)))]) bindings))
	 ~@body))))

#_ (defmacro ds-fn [bindings & body]
  (let [ds (gensym)]
    `(fn [~ds]
       (let ~(vec (interleave bindings (map (fn [b] `(safe-get ~ds ~(keyword (name b)))) bindings)))
	 ~@body))))

(defn ds-derive [f ds new-field]
  (for [x ds]
    (assoc x new-field (f x))))

(defn ds-summarize [ds group-fields field-combiner-extractors]
  (for [[k v] (group-by (fn [d] (vec (map #(get d %) group-fields))) ds)]
    (into {} 
	  (concat
	   (map vector group-fields k)
	   (for [[field combiner extractor] field-combiner-extractors]
	     [field (apply combiner (map extractor v))])))))


(defn ds->chart 
  ([ds group-fields x y] 
     (ds->chart ds group-fields x y 
		{:key "top left" :xlabel x :ylabel y :title (str y " vs " x " grouped by " group-fields)} 
		(constantly {})))
  ([ds group-fields x y chart-options series-option-fn] 
     (ds->chart ds group-fields x y chart-options series-option-fn identity))
  ([ds group-fields x y chart-options series-option-fn series-name-fn] 
     (ds->chart ds group-fields x y chart-options series-option-fn series-name-fn identity))
  ([ds group-fields x y chart-options series-option-fn series-name-fn sort-fn] 
     (apply struct-map chart :series 
       (sort-fn
       (for [[k v] (group-by (fn [d] (vec (map #(get d %) #_ #(safe-get d %) group-fields))) ds)]
         (apply struct-map series :title (series-name-fn k) :data 
		(sort-by first (map (fn [d] [(safe-get d x) (safe-get d y)]) v))
		(mapcat identity (series-option-fn k)))))
       (mapcat identity chart-options))))

	    