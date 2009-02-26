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

(defmacro make-safe 
  ([x] `(make-safe ~x ""))
  ([x format-str & args]
     `(let [x# ~x]
	(when-not x# (throw (Exception. (str (format ~format-str ~@args) 
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

