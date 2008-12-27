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


