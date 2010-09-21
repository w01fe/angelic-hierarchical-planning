(in-ns 'edu.berkeley.ai.util)

(defn min-comparable [& args]
  (assert (seq args))
  (loop [best (first args) rest (next args)]
    (if-let [[f & r] rest]
        (if (neg? (compare f best)) (recur f r) (recur best r))
        best)))

(defn git-commit-id []
  (aget (.split #^String (sh "git" "log" "-1" :dir (root-local "")) "\n") 0))

(def *debug-level* 0)

(defmacro debug [l & body]
  `(binding [*debug-level* ~l] ~@body))

(defn single-quote [s] (str "'" s "'"))

(defn double-quote [s] (str "\"" s "\""))

(defn prog1 [arg & args] (dorun args) arg)

(defmacro with-out-str2
  "Evaluates exprs in a context in which *out* is bound to a fresh
  StringWriter.  Returns [return-val, string]"
  [& body]
  `(let [s# (new java.io.StringWriter)]
     (binding [*out* s#]
       [(do ~@body) (str s#)])))

(defmacro print-debug [level & args]
  `(when (>= @~#'*debug-level* ~level)
    (println ~@args)))

(defn prln "Print all arguments and return the first argument"
  [& args] (do (println (apply print-str args)) (first args)))

(defmacro trace-expr "Trace a single expression, printing info about args and return. Will remove shortcuts"
  ([expr] 
     `(do
        (let [args# (list ~@(next expr))]
	  (print "Entering " (cons '~(first expr) args#) "...\n")
	  (let [result# (apply ~(first expr) args#)]
	    (print "Leaving " (cons '~(first expr) args#) ", got " result# ".\n")
	    result#)))))


(set! *warn-on-reflection* true)

(import '[edu.berkeley.ai.util Double2Arrays] '[java.util List])
(defn to-double2 [#^List ss] (Double2Arrays/toDouble2Array ss))
(defn aset-double2 [#^"[[D" a i j v] (Double2Arrays/set a i j v))
(defn aget-double2 [#^"[[D" a i j] (Double2Arrays/get a i j))


(import '[edu.berkeley.ai.util HungarianAlgorithm])
(defn maximum-matching "Edges are [n1 n2 weight].  Returns weight." 
  ([#^"[[D" arr] (HungarianAlgorithm/hgAlgorithm arr "max"))
  ([left-nodes right-nodes edges]
  (let [left-nodes    (seq left-nodes)
	right-nodes   (seq right-nodes)
	left-node-ids (into {} (map vector left-nodes (iterate inc 0)))
	right-node-ids (into {} (map vector right-nodes (iterate inc 0)))
	n        (count left-node-ids)
	arr      (make-array Double/TYPE n n)]
    (assert-is (= n (count right-node-ids)))
    (doseq [i (range n), j (range n)] (aset-double2 arr i j Double/NEGATIVE_INFINITY))
    (doseq [[n1 n2 v] edges] 
      (let [i1 (int (safe-get left-node-ids n1)),
	    i2 (int (safe-get right-node-ids n2))
	    v  (double v)]
;	(assert-is (= (Double/NEGATIVE_INFINITY) (aget arr i1 i2)))
	(aset-double2 arr i1 i2 v)))
;    (println (map seq (seq arr)))    
    (maximum-matching arr)
    )))
      

(set! *warn-on-reflection* false)	

(comment 
(defn test-maximum-matching [n]
  (let [nn (range n)
	evs (vec (take n (repeatedly (fn [] (vec (take n (repeatedly #(rand-int 10))))))))
	es  (for [i nn, j nn] [i j (nth (nth evs i) j)])
	v   (maximum-matching nn nn es)]
;    (println evs v)
    (assert-is
     (= v 
	(apply max
	  (map (fn [p]
		  (apply +
		    (for [[i v] (map vector p evs)]
		      (nth v i))))
		     (permutations nn)))))))
    )
    



(comment 
(defn pst2
   "Print the stack trace of the \"cause\" of the specified exception or *e if none passed"
   ([] (.printStackTrace (.getCause *e)))
   ([e] (.printStackTrace (.getCause e)))
    ))

(defn symbol-cat [& args]
  (symbol (apply str args)))

(defn desymbolize [symbol n]
  (read-string (apply str (nthnext (name symbol) n))))


(defn symbol-abs-diff [sym1 sym2 n]
  (let [s1 (.substring (name sym1) n)
	s2 (.substring (name sym2) n)]
    (Math/abs (unchecked-subtract (Integer/parseInt s1) (Integer/parseInt s2)))))

(defn desymbolize-int [symbol n]
  (read-string (apply str (nthnext (name symbol) n))))

(defn truthify [x]
  (if x true false))


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
	:else (concat (match-vars (first var-tree)) (match-vars (next var-tree)))))



(defmacro merge-mappings [s1 s2]
  `(when-let [s1# (seq ~s1)]
     (filter identity 
	     (for [m1# s1#, m2# ~s2] (merge-agree m1# m2#)))))

(defmacro merge-multi-mappings [s1 s2]
  `(when-let [s1# (seq ~s1)]
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
;	  (match-mappings [:multiple (nfirst var-tree)] match-tree)
        :else
	  (concat-elts
	   (for [clause var-tree] ; :when (not (= (first clause) :rest))]
	     (if (= (first clause) :multiple)
	         (merge-multi-mappings
		  (match-mappings (second clause) (first match-tree))
		  (match-set      var-tree        (next match-tree)))
	       (merge-mappings
		(match-mappings (if (= :optional (first clause)) (second clause) clause) (first match-tree))
		(match-set      (disj var-tree clause)                                   (next match-tree))))))))

;  "leave match-set " var-tree match-tree))
;	     (match-mappings 
;	      [clause (if (= (first clause) :multiple) var-tree (disj var-tree clause))]
;	      [(first match-tree) (next match-tree)])))))



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
            (do (assert (empty? (next var-tree)))
                [{(second (first var-tree)) match-tree}])
  	  (and (coll? (first var-tree)) (= (ffirst var-tree) :optional))
	    (do (assert-is (= (count (first var-tree)) 2))
		(lazy-cat (merge-mappings (match-mappings (second (first var-tree)) (first match-tree))
					  (match-mappings (next var-tree) (next match-tree)))
			  (match-mappings (next var-tree) match-tree)))
  	  (and (coll? (first var-tree)) (= (ffirst var-tree) :multiple))
	    (do (assert-is (= (count (first var-tree)) 2))
		(lazy-cat (merge-multi-mappings (match-mappings (second (first var-tree)) (first match-tree))
					  (match-mappings var-tree (next match-tree)))
			  (match-mappings (next var-tree) match-tree)))
	  (not (coll? match-tree))
            nil
       	  :else 
	    (merge-mappings (match-mappings (first var-tree) (first match-tree))
			    (match-mappings (next var-tree) (next match-tree))))))

(defn match-mapping [var-tree match-tree]
  (let [matches (match-mappings var-tree match-tree)]
    (when (empty? matches) (throw (IllegalArgumentException. (str "No matches: " var-tree " " (seq match-tree)))))
    (when (next matches) (throw (IllegalArgumentException. (str "Multiple matches: " var-tree " " match-tree "\n" (take 2 matches)))))
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
	   (when (next ~g) (throw (IllegalArgumentException. (str "Multiple matches: " '~var-tree " " ~match-tree "\n" (take 2 ~g)))))
	   (let ~(apply vector (mapcat #(vector % `(get (first ~g) '~% :no-match))  vars))
	     ~then))
	 ~else))))  

(defmacro when-match
  [binding & body]
  `(if-match ~binding (do ~@body) nil))

(defn xor [& args]
  (odd? (count (filter identity args))))
  
(defn same-truth-value? [& args]
  (apply = (map #(when % true) args)))

(defn truth= [& args]
  (apply = (map #(when % true) args)))

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
		 (match-mapping (next var-tree) (next match-tree)))))
  )
 
(defn differences 
  "Take a seq of data structures, and return a seq where all of the matching parts
   have been removed.  Returns nil if the data structures are equal.  Converts all 
   non-set/maps to arbitary seq types."
  [ds]
  (when-first [f ds]
    (cond (map? f)
            (if (every? map? ds)
                (let [ds (map #(into {} %) ds)  ; fix structmaps
                      key-kernel (apply intersection (map keyset ds))
                      reduced-ds (reduce 
                                  (fn [ds k]
                                    (if-let [diffs (differences (map #(% k) ds))]
                                        (map #(assoc %1 k %2) ds diffs)
                                      (map #(dissoc % k) ds)))
                                  ds key-kernel)]
                  (when-not (every? empty? reduced-ds)
                    reduced-ds))
              ds)
          (set? f)
            (if (every? set? ds)
              (let [kernel (apply intersection ds)
                    res (map #(difference % kernel) ds)]
                (when (some seq res) res))
              ds)        
          (instance? clojure.lang.Seqable f)
            (if (every? #(instance? clojure.lang.Seqable %) ds)
                (loop [rest-ds ds out (map (constantly []) ds)]
                  (cond (every? empty? rest-ds)
                          (when-not (every? empty? out) out)
                        (some empty? rest-ds)
                          (map concat out rest-ds)
                        :else 
                          (if-let [d (differences (map first rest-ds))]
                              (recur (map rest rest-ds) (map conj out d))
                            (recur (map rest rest-ds) out))))
              ds)
          :else 
            (when-not (apply = ds) ds))))





; Weak reference sequence -- eventually, do in Java? 

(comment ; Just use WeakHashMap, .put x true, keys.
(import '[java.lang.ref WeakReference] '[java.util ArrayList])

(defn make-weak-ref-seq 
  ([] (make-weak-ref-seq []))
  ([s] (ArrayList. (map #(WeakReference. %) s))))

(defn weak-ref-seq-add! [#^ArrayList s x]
  (.add s (WeakReference. x)))

(defn weak-ref-seq [#^ArrayList s]
  (filter identity (map #(.get #^WeakReference %) (seq s))))
 )

