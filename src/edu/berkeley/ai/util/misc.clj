(in-ns 'edu.berkeley.ai.util)

(defn prln "Print and return the first argument"
  [& args] (do (println (apply print-str args)) (first args)))

(defn pst2
   "Print the stack trace of the \"cause\" of the specified exception or *e if none passed"
   ([] (.printStackTrace (.getCause *e)))
   ([e] (.printStackTrace (.getCause e)))
    )

(defn truthify [x]
  (if x true false))

(defn sref-set! [sref val] 
  (aset sref 0 val))

(defn sref-get [sref]
  (aget sref 0))

(defn sref-up! [sref fn & args]
  (aset sref 0 (apply fn (aget sref 0) args)))

(defn sref "A non-thread-safe, reasonably fast mutable reference"
  ([] (make-array Object 1))
  ([init] (let [ret (sref)] (sref-set! ret init) ret)))


(defn match-vars   "Return a seq of the variables mentioned in the tree."
  [var-tree]
  (cond (not (coll? var-tree)) nil
	(= (first var-tree) 'unquote) [(second var-tree)]
	(and (coll? (first var-tree)) (= (ffirst var-tree) 'unquote-seq)) [(second (first var-tree))]
	:else (concat (match-vars (first var-tree)) (match-vars (rest var-tree)))))



(defn merge-mappings [s1 s2]
  (filter identity 
     (for [m1 s1, m2 s2] (merge-agree m1 m2))))

(declare match-mappings)

(defn match-set [var-tree match-tree]
  (cond (empty? var-tree)
          (when (empty? match-tree) [{}])
	(empty? match-tree)
	  (when (every? #(= (first %) :optional) var-tree) [{}])
        :else
	  (concat-elts
	   (for [clause var-tree]
	     (when-let [dm (match-mappings (if (= (first clause) :optional) (second clause) clause) (first match-tree))]
	       (merge-mappings dm (match-set (remove #(identical? clause %) var-tree) (rest match-tree))))))))

(defn match-mappings "Return a lazy seq of maps of variable bindings for this matching.
                      Binds variables in (unquote x) and (unquote-seq x) - greedy forms, 
                      matches any order for sets, and hangles (:optional ... )"
  [var-tree match-tree]
;  (prn var-tree match-tree)
  (distinct 
    (cond (not (coll? var-tree))
	    (when (= var-tree match-tree)
	      [{}])
	  (set? var-tree)
	    (match-set var-tree match-tree)
	  (= (first var-tree) 'unquote)
	    [{(second var-tree) match-tree}]
	  (and (coll? (first var-tree)) (= (ffirst var-tree) 'unquote-seq))
	    [{(second (first var-tree)) match-tree}]
  	  (and (coll? (first var-tree)) (= (ffirst var-tree) :optional))
	    (do (assert-is (= (count (first var-tree)) 2))
		(lazy-cat (merge-mappings (match-mappings (second (first var-tree)) (first match-tree))
					  (match-mappings (rest var-tree) (rest match-tree)))
			  (match-mappings (rest var-tree) match-tree)))
	  (not (coll? match-tree))
            nil
       	  :else 
	    (merge-mappings (match-mappings (first var-tree) (first match-tree))
			    (match-mappings (rest var-tree) (rest match-tree))))))

(defn match-mapping [var-tree match-tree]
  (let [matches (match-mappings var-tree match-tree)]
    (when (empty? matches) (throw (IllegalArgumentException. (str "No matches: " var-tree " " match-tree))))
    (when (rest matches) (throw (IllegalArgumentException. (str "Multiple matches: " var-tree " " match-tree "\n" (take 2 matches)))))
    (first matches)))

(defmacro match "Take a var-tree with (unquote x) and (unquote-seq y) expressions
                 and match it with match-tree, binding these variables, and
                 throwing an exception if a valid matching cannot be found."
  [[var-tree match-tree] & body]
  (let [vars (match-vars var-tree) g (gensym)]
    `(let [~g (match-mapping '~var-tree ~match-tree)]
       (let ~(apply vector (mapcat #(vector % `(get ~g '~% :no-match))  vars))
	 ~@body))))

(defn xor [& args]
  (odd? (count (filter identity args))))
  

(comment 
  (match-mappings 
   '[[:optional [:FOO [unquote x]]]
     [:BAR [unquote y]]]
   [[:FOO 12] [:BAR 14]])

  (match-mappings
   '#{[:FOO [unquote x]]
      [:BAR [unquote y]]
      [:optional [:BAZ [unquote z]]]}
   [[:FOO 12] [:BAR 14]])   
     

(defn match-mapping "Return a map of variable bindings for this matching, or 
                     throw an error if a matching is not possible."
  [var-tree match-tree]
  (cond (not (coll? var-tree))
	  (when (not= var-tree match-tree)
	    (throw (Exception. (str "Bad Match: " var-tree " " match-tree))))
	(= (first var-tree) 'unquote)
	  {(second var-tree) match-tree}
	(and (coll? (first var-tree)) (= (ffirst var-tree) 'unquote-seq))
	  {(second (first var-tree)) match-tree}
	(not (coll? match-tree))
	  (throw (Exception. (str "Bad Match: " var-tree " " match-tree)))
	:else 
	  (merge (match-mapping (first var-tree) (first match-tree))
		 (match-mapping (rest var-tree) (rest match-tree)))))
  )
 