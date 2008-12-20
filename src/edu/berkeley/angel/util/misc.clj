(ns edu.berkeley.angel.util
  (:import (java.util PriorityQueue HashMap) (com.bluemarsh.graphmaker.core.util FibonacciHeap))
  )

(defn pst2
   "Print the stack trace of the \"cause\" of the specified exception or *e if none passed"
   ([] (.printStackTrace (.getCause *e)))
   ([e] (.printStackTrace (.getCause e)))
    )


(defn make-simple-priority-queue []
  "A mutable priority queue that supports only add and remove-min"
  (new FibonacciHeap))

(defn simple-pq-add! [#^FibonacciHeap pq item cost]
  (.insert pq item cost))

(defn simple-pq-remove-min! [#^FibonacciHeap pq]
  (.removeMin pq))

(defn simple-pq-remove-min-with-cost! [#^FibonacciHeap pq]
  (let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min pq) 
	c (.getKey n)]
    (vector (.removeMin pq) c)))

(defn simple-pq-size [#^FibonacciHeap pq]
  (.size pq))

(defn simple-pq-empty? [#^FibonacciHeap pq]
  (.isEmpty pq))




(defn make-fancy-priority-queue []
  "A slightly slower mutable priority queue that only allows for single instance of each object, maintaining min priority."
  (vector (new HashMap) (new FibonacciHeap)))

(defn fancy-pq-add! [[#^HashMap m #^FibonacciHeap pq] item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert pq item cost)) :added)
	  (< cost (.getKey n)) (do (.decreaseKey pq n cost)        :decreased)
	  true                 :ignored)))

(defn fancy-pq-remove! [[#^HashMap m #^FibonacciHeap pq] item]
  (let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.get m item)]
    (.delete pq n)))

(defn fancy-pq-remove-min! [[#^HashMap m #^FibonacciHeap pq]]
  (let [ret (.removeMin pq)]
    (.remove m ret)
    ret))

(defn fancy-pq-remove-min-with-cost! [[#^HashMap m #^FibonacciHeap pq]]
  (let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min pq) 
	c (.getKey n)
	ret (.removeMin pq)]
    (.remove m ret)
    (vector ret c)))

(defn fancy-pq-size [[#^HashMap m #^FibonacciHeap pq]]
  (.size pq))

(defn fancy-pq-empty? [[#^HashMap m #^FibonacciHeap pq]]
  (.isEmpty pq))

(defn fancy-pq-contains? [[#^HashMap m #^FibonacciHeap pq] item]
  (.containsKey m item))





(defn make-simple-pq [] {:class ::SimplePriorityQueue :heap (new FibonacciHeap)})
(defn make-fancy-pq [] {:class ::FancyPriorityQueue :map (new HashMap) :heap (new FibonacciHeap)})

(defmulti pq-add! (fn [a b c] (:class a)))
(defmulti pq-remove-min! :class)
(defmulti pq-empty? :class)


(defmethod pq-add! ::SimplePriorityQueue [pq item cost]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.insert heap item cost)))

(defmethod pq-remove-min! ::SimplePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.removeMin heap)))

(defmethod pq-empty?  ::SimplePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.isEmpty heap)))


(defmethod pq-add!  ::FancyPriorityQueue [fpq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeap pq (:heap fpq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert pq item cost)) :added)
	  (< cost (.getKey n)) (do (.decreaseKey pq n cost)        :decreased)
	  true                 :ignored)))

(defmethod pq-remove-min! ::FancyPriorityQueue [fpq]
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeap pq (:heap fpq)
	ret (.removeMin pq)]
    (.remove m ret)
    ret))

(defmethod pq-empty? ::FancyPriorityQueue [fpq]
  (let [#^FibonacciHeap pq (:heap fpq)]
    (.isEmpty pq)))









(comment 

 ; Fairly comparable times.  Must wrap either with HaspMap to make usable. (FibHeap slightly slower w/o decreasekeys)
 ; Declaring types makes huge difference (factor of 6!)  (dotimes [_ 3]
    (time (let [#^PriorityQueue pq (new PriorityQueue)]
	    (dotimes [_ 1000000] 
	      (.add pq (rand-int 1000000)))
	    (while (not (.isEmpty pq)) (.poll pq))))
    (time (let [#^FibonacciHeap pq (new FibonacciHeap)]
	    (dotimes [i 1000000] 
	      (.insert pq i (rand-int 1000000)))
	    (while (not (.isEmpty pq)) (.removeMin pq))))



  ; roughlhy same speed, fancy is about 33% slower.
  (dotimes [_ 3]
    (time (let [pq (make-simple-priority-queue)]
	    (dotimes [i 1000000] 
	      (simple-pq-add! pq i (rand-int 1000000)))
	    (while (not (simple-pq-empty? pq)) (simple-pq-remove-min! pq))))
    (time (let [pq (make-fancy-priority-queue)]
	    (dotimes [i 1000000] 
	      (fancy-pq-add! pq i (rand-int 1000000)))
	    (while (not (fancy-pq-empty? pq)) (fancy-pq-remove-min! pq)))))

  ;Check decreasekey, etc.
  (dotimes [_ 3]
    (time (let [pq (make-simple-priority-queue)]
	    (dotimes [i 1000000] 
	      (simple-pq-add! pq (rem i 10) (rand-int 100000)))
	    (loop [i 0] (if (simple-pq-empty? pq) (prn i) (do (simple-pq-remove-min! pq) (recur (inc i)))))))
    (time (let [pq (make-fancy-priority-queue)]
	    (dotimes [i 1000000] 
	      (fancy-pq-add! pq (rem i 10) (rand-int 100000)))
	    (loop [i 0] (if (fancy-pq-empty? pq) (prn i) (do (fancy-pq-remove-min! pq) (recur (inc i))))))))

  ; test method overhead
  (dotimes [_ 3]
    (time (let [pq (make-simple-pq)]
	    (dotimes [i 1000000] 
	      (pq-add! pq i (rand-int 1000000)))
	    (while (not (pq-empty? pq)) (pq-remove-min! pq))))
    (time (let [pq (make-fancy-pq)]
	    (dotimes [i 1000000] 
	      (pq-add! pq i (rand-int 1000000)))
	    (while (not (pq-empty? pq)) (pq-remove-min! pq))))))

