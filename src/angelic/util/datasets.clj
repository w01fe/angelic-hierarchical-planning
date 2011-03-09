(ns angelic.util.datasets
  (:use angelic.util angelic.util.charts clojure.contrib.pprint)
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



;; From http://briancarper.net/blog/printing-a-nicely-formatted-plaintext-table-of-data-in-clojure
(defn table
  "Given a seq of hash-maps, prints a plaintext table of the values of the hash-maps.
  If passed a list of keys, displays only those keys.  Otherwise displays all the
  keys in the first hash-map in the seq."
  ([xs]
     (table xs (keys (first xs))))
  ([xs ks]
     (when (seq xs)
       (let [f (fn [old-widths x]
                 (reduce (fn [new-widths k]
                           (let [length (inc (count (str (k x))))]
                             (if (> length (k new-widths 0))
                               (assoc new-widths k length)
                               new-widths)))
                         old-widths ks))
             widths (reduce f {} (conj xs (zipmap ks ks)))
             total-width (reduce + (vals widths))
             format-string (str "~{"
                                (reduce #(str %1 "~" (%2 widths) "A") "" ks)
                                "~}~%")]
         (cl-format true format-string (map str ks))
         (cl-format true "~{~A~}~%" (repeat total-width \-))
         (doseq [x xs]
           (cl-format true format-string (map x ks)))))))

	    