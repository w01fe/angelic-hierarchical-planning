(in-ns 'edu.berkeley.angel.search.hierarchical)

(defstruct high-level-action :class )

(defmulti immediate-refinements [act]
  )


(defn plug [v pos subseq]
  (append (subvec v 0 pos)
	  subseq
	  (subvec v (inc pos))))

(defmethod immediate-refinements nil [act-seq position]
  (map #(plug act-seq count %) act-seq))

(defmethod immediate-refinements nil [act-seq]
  (concat-elts
   (for [position (range (count act-seq))]
     (immediate-refinements act-seq position)))

(comment 

(let [its (iterate #(subvec % 0 10) (apply vector (range 20)))] 
  (doseq [i (range 0 100 10)] 
    (print i " ")
    (let [sub (nth its i)]
      (time (dotimes [_ 1000000] (sub 5))))))

)