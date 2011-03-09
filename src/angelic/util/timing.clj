(in-ns 'angelic.util)

(set! *warn-on-reflection* true)

(defn make-stopwatch [] 
  {:class ::Stopwatch :started nil :elapsed-ns 0})

(defn start-stopwatch 
  ([] (start-stopwatch (make-stopwatch)))
  ([sw] 
     (assert-is (nil? (:started sw)))
     (assoc sw :started (System/nanoTime))))

(defn stop-stopwatch [sw]
  (assert-is (not (nil? (:started sw))))
  (assoc sw :started nil :elapsed-ns (+ (:elapsed-ns sw) (- (System/nanoTime) (:started sw)))))

(defn get-elapsed-seconds [sw]
  (/ (+ (:elapsed-ns sw)
	(if (:started sw) (- (System/nanoTime) (:started sw)) 0))
     1000000000.0))

(defn within-time-limit? [sw tl]
  (<= (get-elapsed-seconds sw) tl))


(defmacro with-time
  "Evaluates expr, binding its value to v and the time taken (in ms) to tv"
  [tv [v expr] & body]
  `(let [start# (System/nanoTime)
	 ~v     ~expr
	 ~tv    (/ (double (- (System/nanoTime) start#)) 1000000.0)]
     ~@body))

(defmacro get-time [expr] `(with-time t# [_# ~expr] t#))

(defmacro get-time-pair [expr] `(with-time t# [v# ~expr] [v# t#]))

(defn- ft [x] (apply str (drop-last 3 (format "%f" x))))

(defn microbench*
  [{:keys [warmup-time min-runs min-time]} body-fn]
  (let [warmup-watch (start-stopwatch)]
;    (println warmup-time min-runs min-time (body-fn))
       (while (within-time-limit? warmup-watch warmup-time) (body-fn))
       (let [main-watch (start-stopwatch)
             times      (loop [times nil runs min-runs]
                          (if (and (<= runs 0) 
                                   (not (within-time-limit? main-watch min-time)))
                              times
                            (recur (cons (get-time (body-fn)) times) (dec runs))))]
;         (println "Params: " params) 
         (println "min; avg; max ms: " 
                  (ft (apply min times)) ";"
                  (ft (/ (apply + times) (count times))) ";"
                  (ft (apply max times))
                  "   (" (count times) " iterations)"
                  ))))

(defmacro microbench
  "Microbenchmark a body.  Takes optional map first argument, with keys
   :warmup-time, :min-runs, :min-time."
  ([form & body]
     (let [defaults {:warmup-time 1 :min-runs 3 :min-time 2}
           [params body] (if (map? form) [(merge defaults form) body] [defaults (cons form body)])
           body-fn `(fn [] ~@body)]
        
       `(microbench* ~params ~body-fn))))


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

(defn timeout "Call this periodically to make sure thread can be interrupted." []
  (when (Thread/interrupted) (throw (InterruptedException.))))

; Thread/sleep 0 1 (slows down a LOT, 10x).  0,0 does not do the job.


(defn kill-future [#^ExecutorService pool #^Future f]
;  (println "killing")
  (.cancel f true)
  (.shutdownNow pool)
  (when-not (.awaitTermination pool 10 java.util.concurrent.TimeUnit/SECONDS)
    (println "shutdown failed")))

(defmacro time-limit
  "Runs expr for at most max-seconds, killing and returning :timeout if out of time,
   otherwise returning [returned-value time-took].  Expr may still execute for awhile after return"
  [expr max-seconds]
  `(let [out# *out*
	 #^ExecutorService pool# (java.util.concurrent.Executors/newCachedThreadPool)
	 #^Callable f#    #(binding [*out* out#] (get-time-pair ~expr))
	 #^Future future# (.submit pool# f#)]
    (try (let [v# (.get future# (long (* 1000 ~max-seconds)) java.util.concurrent.TimeUnit/MILLISECONDS)]
	   (if (< (second v#) (* 1000 ~max-seconds)) v# :timeout2))	   
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
	 out# *out*
	 #^Callable f#    #(binding [*out* out#] (get-time-pair ~expr))
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
	 out# *out*
	 #^Callable f#    #(binding [*out* out#] (get-time-pair ~expr))
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


;; When we're actually timing, we need to warmup first.

(defmacro warm-up "Run expr until at least min-secs have elapsed, default 10." 
  ([expr] `(warm-up ~expr 10))
  ([expr min-secs] 
     `(let [c# (counter-from 0)]
	(time-limit (while true (timeout) (c#) ~expr) ~min-secs)
	(dec (c#)))))

(defmacro with-warm-up [expr min-secs time-macro & macro-args]
  `(do (warm-up ~expr ~min-secs)
       (~time-macro ~expr ~@macro-args)))


(defn interrupt-all-threads []
  (doseq [#^Thread thread (.keySet (Thread/getAllStackTraces))]
    (.interrupt thread)))

	 
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
  


