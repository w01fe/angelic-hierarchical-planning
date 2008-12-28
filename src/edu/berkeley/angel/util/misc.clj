(in-ns 'edu.berkeley.angel.util)

(defn pst2
   "Print the stack trace of the \"cause\" of the specified exception or *e if none passed"
   ([] (.printStackTrace (.getCause *e)))
   ([e] (.printStackTrace (.getCause e)))
    )

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

(defmacro match "Take a var-tree with (unquote x) and (unquote-seq y) expressions
                 and match it with match-tree, binding these variables, and
                 throwing an exception if a valid matching cannot be found."
  [[var-tree match-tree] & body]
  (let [vars (match-vars var-tree) g (gensym)]
    `(let [~g (match-mapping '~var-tree ~match-tree)]
       (let ~(apply vector (mapcat #(vector % `(safe-get ~g '~%))  vars))
	 ~@body))))


  

