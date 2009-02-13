(in-ns 'edu.berkeley.ai.util)

(defn prln "Print all arguments and return the first argument"
  [& args] (do (println (apply print-str args)) (first args)))

(defmacro trace-expr "Trace a single expression, printing info about args and return. Will remove shortcuts"
  ([expr] 
     `(do
        (let [args# (list ~@(rest expr))]
	  (print "Entering " (cons '~(first expr) args#) "...\n")
	  (let [result# (apply ~(first expr) args#)]
	    (print "Leaving " (cons '~(first expr) args#) ", got " result# ".\n")
	    result#)))))



(comment 
(defn pst2
   "Print the stack trace of the \"cause\" of the specified exception or *e if none passed"
   ([] (.printStackTrace (.getCause *e)))
   ([e] (.printStackTrace (.getCause e)))
    ))

(defn symbol-cat [& args]
  (symbol (apply str args)))

(defn desymbolize [symbol n]
  (read-string (apply str (nthrest (name symbol) n))))

(import '(java.io File))

(def *local-root*
  (let [my-path (.getParent (.getAbsoluteFile (File. ".")))
	my-suffix (.getParent (File. *file*))]
    (assert-is (.endsWith my-path my-suffix))
    (.substring my-path 0 (- (count my-path) (count my-suffix)))))

(defn path-local [s]
  (str *local-root* (.getParent (File. *file*)) "/" s))

(defn symbol-abs-diff [sym1 sym2 n]
  (let [s1 (.substring (name sym1) n)
	s2 (.substring (name sym2) n)]
    (Math/abs (unchecked-subtract (Integer/parseInt s1) (Integer/parseInt s2)))))

(defn desymbolize-int [symbol n]
  (read-string (apply str (nthrest (name symbol) n))))

(defn truthify [x]
  (if x true false))

(comment ; old version -- faster, but fouls up YourKit
(defn sref-set! [sref val] 
  (aset sref 0 val))

(defn sref-get [sref]
  (aget sref 0))

(defn sref-up! [sref fn & args]
  (aset sref 0 (apply fn (aget sref 0) args)))

(defn sref "A non-thread-safe, reasonably fast mutable reference"
  ([] (make-array Object 1))
  ([init] (let [ret (sref)] (sref-set! ret init) ret)))
  )


;(comment ;; New versions - slower, but better for profiling.  TODO: switch back.
(defn sref-set! [sref val] 
  (reset! sref val))

(defn sref-get [sref]
  @sref)

(defn sref-up! [sref fn & args]
  (reset! sref (apply fn @sref args)))

(defn sref "A non-thread-safe, reasonably fast mutable reference"
  ([] (sref nil))
  ([init] (atom init)))
;  )

(defn match-vars   "Return a seq of the variables mentioned in the tree."
  [var-tree]
  (cond (not (coll? var-tree)) nil
	(= (first var-tree) 'clojure.core/unquote) [(second var-tree)]
	(and (coll? (first var-tree)) (= (ffirst var-tree) 'clojure.core/unquote-splicing)) [(second (first var-tree))]
	:else (concat (match-vars (first var-tree)) (match-vars (rest var-tree)))))



(defmacro merge-mappings [s1 s2]
  `(when-let [s1# ~s1]
     (filter identity 
	     (for [m1# s1#, m2# ~s2] (merge-agree m1# m2#)))))

(defmacro merge-multi-mappings [s1 s2]
  `(when-let [s1# ~s1]
     (for [m1# s1#, m2# ~s2] 
       (reduce (fn [m# [k# v#]] (assoc m# k# (cons v# (get m# k#)))) m2# m1#))))

(declare match-mappings)

(defn match-set [var-tree match-tree]
;  (prn "enter match-set " var-tree match-tree)
  (cond (empty? var-tree)
          (when (empty? match-tree) [{}])
	(empty? match-tree)
	  (when (every? #(contains? #{:optional :multiple} (first %)) var-tree) [{}])
;	(and (= (count var-tree) 1) (= (ffirst var-tree) :rest))
;	  (match-mappings [:multiple (rfirst var-tree)] match-tree)
        :else
	  (concat-elts
	   (for [clause var-tree] ; :when (not (= (first clause) :rest))]
	     (if (= (first clause) :multiple)
	         (merge-multi-mappings
		  (match-mappings (second clause) (first match-tree))
		  (match-set      var-tree        (rest match-tree)))
	       (merge-mappings
		(match-mappings (if (= :optional (first clause)) (second clause) clause) (first match-tree))
		(match-set      (disj var-tree clause)                                   (rest match-tree))))))))

;  "leave match-set " var-tree match-tree))
;	     (match-mappings 
;	      [clause (if (= (first clause) :multiple) var-tree (disj var-tree clause))]
;	      [(first match-tree) (rest match-tree)])))))



(defn match-mappings "Return a lazy seq of maps of variable bindings for this matching.
                      Binds variables in (clojure.core/unquote x) and (clojure.core/unquote-splicing x) - greedy forms, 
                      matches any order for sets, and hangles (:optional ... )"
  [var-tree match-tree]
 ; (prn "match-mappings " var-tree match-tree)
  (distinct 
    (cond (not (coll? (seq-coll var-tree)))
	    (when (= (seq-coll var-tree) (seq-coll match-tree))
	      [{}])
	  (set? var-tree)
	    (match-set var-tree match-tree)
	  (= (first var-tree) 'clojure.core/unquote)
	    [{(second var-tree) match-tree}]
	  (and (coll? (first var-tree)) (= (ffirst var-tree) 'clojure.core/unquote-splicing))
	    [{(second (first var-tree)) match-tree}]
  	  (and (coll? (first var-tree)) (= (ffirst var-tree) :optional))
	    (do (assert-is (= (count (first var-tree)) 2))
		(lazy-cat (merge-mappings (match-mappings (second (first var-tree)) (first match-tree))
					  (match-mappings (rest var-tree) (rest match-tree)))
			  (match-mappings (rest var-tree) match-tree)))
  	  (and (coll? (first var-tree)) (= (ffirst var-tree) :multiple))
	    (do (assert-is (= (count (first var-tree)) 2))
		(lazy-cat (merge-multi-mappings (match-mappings (second (first var-tree)) (first match-tree))
					  (match-mappings var-tree (rest match-tree)))
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

(defmacro match "Take a var-tree with (clojure.core/unquote x) and (clojure.core/unquote-splicing y) expressions
                 and match it with match-tree, binding these variables, and
                 throwing an exception if a valid matching cannot be found."
  [[var-tree match-tree] & body]
  (let [vars (match-vars var-tree) g (gensym)]
    `(let [~g (match-mapping '~var-tree ~match-tree)]
       (let ~(apply vector (mapcat #(vector % `(get ~g '~% nil))  vars))
	 ~@body))))

(defmacro if-match 
  [[var-tree match-tree] then else]
  (let [vars (match-vars var-tree) g (gensym)]
    `(let [~g (match-mappings '~var-tree ~match-tree)]
       (if (first ~g)
	 (do 
	   (when (rest ~g) (throw (IllegalArgumentException. (str "Multiple matches: " '~var-tree " " ~match-tree "\n" (take 2 ~g)))))
	   (let ~(apply vector (mapcat #(vector % `(get (first ~g) '~% :no-match))  vars))
	     ~then))
	 ~else))))  

(defmacro when-match
  [binding & body]
  `(if-match ~binding (do ~@body) nil))

(defn xor [& args]
  (odd? (count (filter identity args))))
  

(comment 
  (match-mappings 
   '[[:optional [:FOO [clojure.core/unquote x]]]
     [:BAR [clojure.core/unquote y]]]
   [[:FOO 12] [:BAR 14]])

  (match-mappings
   '#{[:FOO ~x]
      [:BAR ~y]
      [:optional [:BAZ ~z]]}
   [[:FOO 12] [:BAR 14]])

  (match-mappings
   '#{[:FOO [clojure.core/unquote x]]
      [:BAR [clojure.core/unquote y]]
      [:multiple [:BAZ [clojure.core/unquote z]]]}
   [[:FOO 12] [:BAR 14]])
     

(defn match-mapping "Return a map of variable bindings for this matching, or 
                     throw an error if a matching is not possible."
  [var-tree match-tree]
  (cond (not (coll? var-tree))
	  (when (not= (seq var-tree) (seq match-tree))
	    (throw (Exception. (str "Bad Match: " var-tree " " match-tree))))
	(= (first var-tree) 'clojure.core/unquote)
	  {(second var-tree) match-tree}
	(and (coll? (first var-tree)) (= (ffirst var-tree) 'clojure.core/unquote-splicing))
	  {(second (first var-tree)) match-tree}
	(not (coll? match-tree))
	  (throw (Exception. (str "Bad Match: " var-tree " " match-tree)))
	:else 
	  (merge (match-mapping (first var-tree) (first match-tree))
		 (match-mapping (rest var-tree) (rest match-tree)))))
  )
 

(import '(java.io ObjectInputStream FileInputStream ObjectOutputStream FileOutputStream))

(defn slurp-object [f]
  (.readObject (ObjectInputStream. (FileInputStream. f))))

(defn spit-object [f o]
  (.writeObject (ObjectOutputStream. (FileOutputStream. f)) o))

