(in-ns 'edu.berkeley.ai.util)

(set! *warn-on-reflection* true)


(defmacro with-time
  "Evaluates expr, binding its value to v and the time taken (in ms) to tv"
  [tv [v expr] & body]
  `(let [start# (System/nanoTime)
	 ~v     ~expr
	 ~tv    (/ (double (- (System/nanoTime) start#)) 1000000.0)]
     ~@body))

(defmacro get-time [expr] `(with-time t# [_# ~expr] t#))

(defmacro get-time-pair [expr] `(with-time t# [v# ~expr] [v# t#]))



(import '(java.util.concurrent ExecutorService Executors Future TimeUnit TimeoutException))
(import '(java.lang.management ManagementFactory MemoryMXBean MemoryUsage))

(def #^MemoryMXBean *mxbean* (ManagementFactory/getMemoryMXBean))
(def #^Runtime      *runtime* (Runtime/getRuntime))

(defn force-gc [] (.gc *runtime*))

(defn get-used-heap-bytes []
  (.getUsed (.getHeapMemoryUsage *mxbean*)))

(defn get-max-heap-bytes 
  ([old-max] (get-max-heap-bytes old-max 1))
  ([old-max max-gc]
     (let [cur-mem (get-used-heap-bytes)]
       (cond (< cur-mem old-max) old-max
	     (zero? max-gc)      cur-mem
	     :else               (do (force-gc) (recur old-max (dec max-gc)))))))

(defn kill-future [#^ExecutorService pool #^Future f]
  (.cancel f true)
  (.shutdownNow pool)
  (.awaitTermination pool 10 java.util.concurrent.TimeUnit/SECONDS))

(defmacro time-limit
  "Runs expr for at most max-seconds, killing and returning :timeout if out of time,
   otherwise returning [returned-value time-took].  Expr may still execute for awhile after return"
  [expr max-seconds]
  `(let [#^ExecutorService pool# (java.util.concurrent.Executors/newCachedThreadPool)
	 #^Callable f#    #(get-time-pair ~expr)
	 #^Future future# (.submit thread-pool# f#)]
    (try (.get future# (long (* 1000 ~max-seconds)) java.util.concurrent.TimeUnit/MILLISECONDS)
	 (catch java.util.concurrent.TimeoutException e# 
	   (kill-future pool# future#)
	   :timeout))))

(defmacro time-and-memory-limit
  "Runs expr for at most max-seconds, allowing at most max-time seconds and max-mb megabytes,
   killing and returning :timeout if out of time, :memout if out of memory, otherwise
   [returned-value ms-took].  Memory limiting may introduce significant, unpredictable
   time overhead when near limit, and will not work for short-running tasks."
  [expr max-seconds max-mb]
  `(let [#^ExecutorService pool# (java.util.concurrent.Executors/newCachedThreadPool)
	 start-mem# (do (dotimes [_# 3] (force-gc)) (get-used-heap-bytes))
	 limit-mem#  (+ start-mem# (* ~max-mb 1024 1024))
	 start-time# (System/nanoTime)
	 limit-time# (+ start-time# (* 1000000000 ~max-seconds)) 
	 #^Callable f#    #(get-time-pair ~expr)
	 #^Future future# (.submit pool# f#)]
     (loop []
       (if-let [v# 
		(try 
		 (.get future# 1 java.util.concurrent.TimeUnit/SECONDS)
		 (catch java.util.concurrent.TimeoutException e# nil))]
	   (if (< (second v#) (* 1000 ~max-seconds)) v# :timeout)
	 (cond (> (System/nanoTime) limit-time#)                (do (kill-future pool# future#) :timeout)
	       (> (get-max-heap-bytes limit-mem# 2) limit-mem#) (do (kill-future pool# future#) :memout)
	       :else (recur))))))


(defmacro time-and-memory-instrument
  "Runs expr for at most max-seconds, allowing at most max-time seconds and max-mb megabytes,
   killing and returning :timeout if out of time, :memout if out of memory, otherwise
   [returned-value ms-took mb-used].  Memory instrumenting may introduce significant, unpredictable
   time overhead, and will not work for short-running tasks.  Initial overhead of up to a second,
   which will also clobber the cache."
  [expr max-seconds max-mb]
  `(let [#^ExecutorService pool# (java.util.concurrent.Executors/newCachedThreadPool)
	 start-mem# (do (dotimes [_# 3] (force-gc)) (get-used-heap-bytes))
	 limit-mem#  (+ start-mem# (* ~max-mb 1024 1024))
	 start-time# (System/nanoTime)
	 limit-time# (+ start-time# (* 1000000000 ~max-seconds)) 
	 #^Callable f#    #(get-time-pair ~expr)
	 #^Future future# (.submit pool# f#)]
     (loop [max-mem# start-mem#]
       (if-let [v# 
		(try 
		 (conj (.get future# 1 java.util.concurrent.TimeUnit/SECONDS)
		       (/ (- max-mem# start-mem#) 1024.0 1024.0))
		 (catch java.util.concurrent.TimeoutException e# nil))]
	   (if (< (second v#) (* 1000 ~max-seconds)) v# :timeout)
	 (if (> (System/nanoTime) limit-time#) 
	     (do (kill-future pool# future#) :timeout)
	   (let [new-max-mem# (get-max-heap-bytes max-mem# 1)]
	     (if (< new-max-mem# limit-mem#) 
		 (recur new-max-mem#)
	       (let [new-max-mem# (get-max-heap-bytes max-mem# 1)]
		 (if (< new-max-mem# limit-mem#)
 		     (recur new-max-mem#)
		   (do (kill-future pool# future#) :memout))))))))))


	 
; Idea for profiling: once a second,
 ; If memory is above previous maximum,
 ;   run gc
 ;   If still above max, record as new max
 ;   If above ceiling, run gc again. 
 ;     If still above ceiling, quit.
;   If above ceiling, run gc again.  I

; Equivalent to above.
;(defn get-used-bytes2 []
;  (- (.totalMemory *runtime*) (.freeMemory *runtime*)))

;(do (println (get-used-bytes2) (get-used-heap-bytes)) (doseq [i [1 2 10 100]] (time (dotimes [_ i] (force-gc))) (println (get-used-bytes2) (get-used-heap-bytes))))
; Usually one time suffices, sometimes you need 2. ..  
  


(set! *warn-on-reflection* false)
  

