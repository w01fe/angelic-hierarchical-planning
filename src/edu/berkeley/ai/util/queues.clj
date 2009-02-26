(ns edu.berkeley.ai.util.queues
  (:refer-clojure)
  (:import (java.util PriorityQueue HashMap HashSet) (com.bluemarsh.graphmaker.core.util FibonacciHeap)) 
;	   (edu.berkeley.ai.util DelayedSeq))  ; only for old clj
  (:use edu.berkeley.ai.util)
  )
  

; Priority queues. 
; BEWARE; some of these will not save you from GHI-type problems. (depth-limited search).


; Priority queues for searching

(defmulti pq-add! (fn [a b c] (:class a)))
(defmulti pq-remove-min! :class)
(defmulti pq-remove-min-with-cost! :class)
(defmulti pq-empty? :class)
(defmulti pq-size :class)
(defmulti pq-add-all! (fn [a b] (:class a)))
(defmethod pq-add-all! ::PriorityQueue [pq items]
  (doseq [[item cost] items] (pq-add! pq item cost)))
(defmulti pq-remove-all! :class)
(defmethod pq-remove-all! ::PriorityQueue [pq]
  (loop [ret []]
    (if (pq-empty? pq) 
      ret
      (recur (conj ret (pq-remove-min-with-cost! pq))))))


(derive ::QueuePriorityQueue ::PriorityQueue)

(defn make-queue-pq 
  "A queue, which ignores priorities"
  [] {:class ::QueuePriorityQueue :queue (sref clojure.lang.PersistentQueue/EMPTY)})

(defmethod pq-add! ::QueuePriorityQueue [pq item cost]
  (sref-up! (:queue pq) conj [item cost])
  :added)

(defmethod pq-remove-min! ::QueuePriorityQueue [pq]
  (let [r (:queue pq)
	ret (peek (sref-get r))]
    (sref-up! r pop)
    (first ret)))

(defmethod pq-remove-min-with-cost! ::QueuePriorityQueue [pq]
  (let [r (:queue pq)
	ret (peek (sref-get r))]
    (sref-up! r pop)
    ret))

(defmethod pq-empty?  ::QueuePriorityQueue [pq]
  (empty? (sref-get (:queue pq))))

(defmethod pq-size  ::QueuePriorityQueue [pq]
  (count (sref-get (:queue pq))))


(derive ::GraphQueuePriorityQueue ::QueuePriorityQueue)

(defn make-graph-queue-pq
  "A queue that ignores priorities and repeated adds of >= priority."
  [] {:class ::GraphQueuePriorityQueue :queue (sref clojure.lang.PersistentQueue/EMPTY) :map (new HashMap)})

(defmethod pq-add! ::GraphQueuePriorityQueue [pq item cost]
  (let [#^HashMap m (:map pq)
	val (.get m item)] 
    (if (and val (<= val cost)) 
        :ignored
      (do (.put m item cost)
	  (sref-up! (:queue pq) conj [item cost])
	  :added)))) 



(derive ::StackPriorityQueue ::PriorityQueue)

(defn make-stack-pq 
  "A stack, which ignores priorities"
  [] {:class ::StackPriorityQueue :stack (sref nil)})

(defmethod pq-add! ::StackPriorityQueue [pq item cost]
  (sref-up! (:stack pq) conj [item cost])
  :added)

(defmethod pq-add-all! ::StackPriorityQueue [pq items]
  (let [old (sref-get (:stack pq))]
    (sref-set! (:stack pq) (concat items old))
    nil))

(defmethod pq-remove-min! ::StackPriorityQueue [pq]
;  (print " r ")
  (let [r (:stack pq)
	val (sref-get r)
	ret (first val)]
    (sref-set! r (rest val))
    (first ret)))

(defmethod pq-remove-min-with-cost! ::StackPriorityQueue [pq]
  (let [r (:stack pq)
	val (sref-get r)
	ret (first val)]
;	ret (first (sref-get r))]
    (sref-set! r (rest val))
;    (sref-up! r next)
    ret))

(defmethod pq-empty?  ::StackPriorityQueue [pq]
  (empty? (sref-get (:stack pq))))

(defmethod pq-size  ::StackPriorityQueue [pq]
  (count (sref-get (:stack pq))))


(derive ::GraphStackPriorityQueue ::StackPriorityQueue)

(defn make-graph-stack-pq
  "A stack that ignores priorities and repeated adds.  BEWARE of GHI with, e.g., depth-limited search."
  [] {:class ::GraphStackPriorityQueue :stack (sref nil) :map (new HashMap)})

(defmethod pq-add! ::GraphStackPriorityQueue [pq item cost]
  (let [#^HashMap m (:map pq)
	val (.get m item)] 
    (if (and val (<= val cost)) 
        :ignored
      (do (.put m item cost)
	  (sref-up! (:stack pq) conj [item cost])
	  :added))))

(defmethod pq-add-all! ::GraphStackPriorityQueue [pq items]
;  (print " a ")
  (let [#^HashMap m (:map pq)
	old (sref-get (:stack pq))]
    (sref-set! (:stack pq) 
	       (concat (for [pair items :when (let [v (.get m (first pair))] 
							   (or (nil? v) (< (second pair) v)))] 
				    (do (.put m (first pair) (second pair)) pair))
				  old))
;    (print " ae ")
    nil))






(derive ::TreePriorityQueue ::PriorityQueue)

(defn make-tree-search-pq 
  "Supports only add! and remove-min!, each item is added regardless of relation to previous objects" 
  [] {:class ::TreePriorityQueue :heap (new FibonacciHeap)})

(defmethod pq-add! ::TreePriorityQueue [pq item cost]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.insert heap item cost)
    :added))

(defmethod pq-remove-min! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.removeMin heap)))

(defmethod pq-remove-min-with-cost! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min heap) 
	c (.getKey n)]
    (vector (.removeMin heap) c)))

(defmethod pq-empty?  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.isEmpty heap)))

(defmethod pq-size  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.size heap)))


(derive ::SafeTreePriorityQueue ::TreePriorityQueue)

(defn make-safe-tree-search-pq []
  (assoc (make-tree-search-pq) 
    :last-min (sref Double/NEGATIVE_INFINITY)
    :class ::SafeTreePriorityQueue))

(defmethod pq-remove-min! ::SafeTreePriorityQueue [pq] (first (pq-remove-min-with-cost! pq) ))

(defmethod pq-remove-min-with-cost! ::SafeTreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min heap) 
	c (.getKey n)]
    (assert-is (>= c (sref-get (:last-min pq))))
    (sref-set! (:last-min pq) c)
    (vector (.removeMin heap) c)))


(derive ::GraphPriorityQueue ::PriorityQueue)

(defn make-graph-search-pq 
  "For graph search with consistent heuristic.  Remembers everything ever added, each removed at most once."
  [] {:class ::GraphPriorityQueue :map (new HashMap) :heap (new FibonacciHeap)})


(defmethod pq-add!  ::GraphPriorityQueue [pq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeap heap (:heap pq)
	n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert heap item cost)) :added)
	  (number? n)          (if (< cost n)
				   (throw (IllegalArgumentException. "Heuristic inconsistency detected."))
				 :ignored)
	  (let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n n] 
		(< cost (.getKey n))) 
		(let [#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n n]
				 (do (.decreaseKey heap n cost)        :decreased))
	  true                 :ignored)))

(defmethod pq-remove-min! ::GraphPriorityQueue [pq]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeap heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min heap) 
	c (.getKey n)
	ret (.removeMin heap)]
    (.put m ret c)
    ret))

(defmethod pq-remove-min-with-cost! ::GraphPriorityQueue [pq]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeap heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.min heap) 
	c (.getKey n)
	ret (.removeMin heap)]
    (.put m ret c)
    (vector ret c)))

(defmethod pq-empty? ::GraphPriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.isEmpty heap)))

(defmethod pq-size ::GraphPriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.size heap)))




(comment 
  (let [queues [(make-queue-pq) (make-graph-queue-pq)
		(make-stack-pq) (make-graph-stack-pq)
		(make-tree-search-pq) (make-graph-search-pq)]
	args (map vector (take 10 (repeatedly #(rand-int 10)))
		         (take 10 (repeatedly #(rand-int 10))))]
    (prn args)
    (doseq [queue queues]
      (prn (:class queue))
      (pq-add-all! queue args)
      (prn (pq-remove-all! queue))
      (doseq [a args] (pq-add! queue (first a) (second a)))
      (prn (pq-remove-all! queue)))))



















; Old versions

(comment 

  

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





(defn make-simple-pq [] {:class ::TreePriorityQueue :heap (new FibonacciHeap)})
(defn make-fancy-pq [] {:class ::GraphPriorityQueue :map (new HashMap) :heap (new FibonacciHeap)})

(defmulti pq-add! (fn [a b c] (:class a)))
(defmulti pq-remove-min! :class)
(defmulti pq-empty? :class)


(defmethod pq-add! ::TreePriorityQueue [pq item cost]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.insert heap item cost)))

(defmethod pq-remove-min! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.removeMin heap)))

(defmethod pq-empty?  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeap heap (:heap pq)]
    (.isEmpty heap)))


(defmethod pq-add!  ::GraphPriorityQueue [fpq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeap pq (:heap fpq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeap$Node n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert pq item cost)) :added)
	  (< cost (.getKey n)) (do (.decreaseKey pq n cost)        :decreased)
	  true                 :ignored)))

(defmethod pq-remove-min! ::GraphPriorityQueue [fpq]
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeap pq (:heap fpq)
	ret (.removeMin pq)]
    (.remove m ret)
    ret))

(defmethod pq-empty? ::GraphPriorityQueue [fpq]
  (let [#^FibonacciHeap pq (:heap fpq)]
    (.isEmpty pq)))


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

