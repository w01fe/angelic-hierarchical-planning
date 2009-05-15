(in-ns 'edu.berkeley.ai.util)

(defmacro forcat 
  "Like for, but concatenates the results."
  [& args]
  `(concat-elts (for ~@args)))

(defmacro assert-is
  "Like assert, but prints some more info about the offending form (may multiple eval on error)"
  ([form] `(assert-is ~form ""))
  ([form format-str & args]
     `(when-not ~form
	(throw (Exception. (str (format ~format-str ~@args) 
				": Got " '~form " as " (cons '~(first form) (list ~@(next form)))))))))
(def *bad-form* (atom nil))
(defmacro make-safe 
  ([x] `(make-safe ~x ""))
  ([x format-str & args]
     `(let [x# ~x]
	(when-not x# 
	  (swap! *bad-form* (constantly (list ~@x)))
	  (throw (Exception. (str (format ~format-str ~@args) 
					     ": False/nil " x# " from " '~x " as " (cons '~(first x) (list ~@(next x)))))))
	x#)))

(defmacro assert-let
  "Like when-let, but , but prints some more info about the offending form (may multiple eval on error)"
  [binding & body]
  (let [binding-form (get binding 0)
	test         (get binding 1)
	format-str   (or (get binding 2) "")
	rest-args    (nthnext binding 3)]
    `(when-let [~binding-form (make-safe ~test ~format-str ~@rest-args)] ~@body)))    
;  ([[binding-form test] & body] `(assert-let [~binding-form ~test ""] ~@body))
;  ([[binding-form test format-str & args] & body]
;     `(when-let [~binding-form (make-safe ~test ~format-str ~@args)] ~@body)))


(defmacro cond-list "Takes args like hash-map, returns lazy seq of elts with true preds."
  ([] ())
  ([pred elt & args]
     `(let [r# (cond-list ~@args)]
	(if ~pred (cons ~elt r#) r#)))) 

(declare distinct-elts? position)
(defmacro parse-optional-argmap 
  "Takes a map and set of bindings.  Each (required unique) var in bindings
   is bound to the corresponding keyword mapping in m, or to the result of the 
   value expression otherwise, for body.  Expressions are evaluated sequentially, and may
   use previous bindings.  It is an error if m contains unbound keys."
  [m bindings & body]
  (assert (even? (count bindings)))
  (let [bindings (partition 2 bindings)
	mg (gensym)]
    (assert (distinct-elts? (map #(keyword (str (first %))) bindings)))
    `(let ~(into [mg m] 
		 (apply concat
		   (map (fn [[k v]] [k `(or (get ~mg ~(keyword (str k))) ~v) 
				     mg `(dissoc ~mg ~(keyword (str k)))]) bindings)))  
       (assert-is (empty? ~mg))
       ~@body)))

(defmacro defn-opt
  "Like defn, but things following & are pairs of optional things.  Optional last-item holds input map."
  [name & fargs]
  (let [[doc-string bindings body]
	(if (string? (first fargs)) 
	    [(first fargs) (second fargs) (nthnext fargs 2)]
	  ["" (first fargs) (next fargs)])
	doc-string (str doc-string "\n" bindings)
	split-pos  (or (position '& bindings) (count bindings))
        norm-args  (vec (take split-pos bindings))
	opt-args   (vec (drop (inc split-pos) bindings))
	[g opt-args] (if (odd? (count opt-args))
		         [(last opt-args) (drop-last 1 opt-args)]
		       [(gensym) opt-args])]	
    `(defn ~name ~doc-string
       (~norm-args (~name ~@norm-args {}))
       (~(conj norm-args g) 
	(parse-optional-argmap ~g ~opt-args ~@body))))) 