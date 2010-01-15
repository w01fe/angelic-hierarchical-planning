(ns edu.berkeley.ai.util.queues
  (:refer-clojure)
  (:import (java.util PriorityQueue HashMap IdentityHashMap HashSet) (com.bluemarsh.graphmaker.core.util FibonacciHeapComp FibonacciHeapComp$Node)) 
;	   (edu.berkeley.ai.util DelayedSeq))  ; only for old clj
  (:use edu.berkeley.ai.util clojure.test)
  )
  

; Priority queues. 
; BEWARE; some of these will not save you from GHI-type problems. (depth-limited search).
; cost can be any Comparable object, to enable tiebreaking.  For the fancier queues that keep track of 
; a "best" cost, the get-cost method will be called to get the actual cost from the object.
; By default, this is the number itself for a number, or the first element of a vector.

(defmulti get-cost class)
(defmethod get-cost Number [x] x)
(defmethod get-cost clojure.lang.IPersistentVector [x] (nth x 0))

; Priority queues for searching

(defmulti pq-add! (fn [pq item cost] (:class pq)))
(defmulti pq-replace! (fn [pq item cost] (:class pq)))  ; a forced version of add.
(defmulti pq-remove! (fn [pq item] (:class pq)))
(defmulti pq-peek-min :class)
(defmulti pq-remove-min-with-cost! :class)
(defmulti pq-size :class)

(defmulti pq-empty? :class)
(defmethod pq-empty? ::PriorityQueue [pq]
  (zero? (pq-size pq)))

(defmulti pq-remove-min! :class)
(defmethod pq-remove-min! ::PriorityQueue [pq]
  (nth (pq-remove-min-with-cost! pq) 0))

(defmulti pq-add-all! (fn [a b] (:class a)))
(defmethod pq-add-all! ::PriorityQueue [pq items]
  (doseq [[item cost] items] (pq-add! pq item cost)))

(defmulti pq-remove-all! :class)
(defmethod pq-remove-all! ::PriorityQueue [pq]
  (loop [ret []]
    (if (pq-empty? pq) 
      ret
      (recur (conj ret (pq-remove-min-with-cost! pq))))))

(defmulti pq-peek-pairs :class)



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

(deftest queue-pq 
  (let [pq (make-queue-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [2 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) items))))



(derive ::GraphQueuePriorityQueue ::QueuePriorityQueue)

(defn make-graph-queue-pq
  "A queue that ignores priorities and repeated adds of >= cost"
  [] {:class ::GraphQueuePriorityQueue :queue (sref clojure.lang.PersistentQueue/EMPTY) :map (new HashMap)})

(defmethod pq-add! ::GraphQueuePriorityQueue [pq item cost]
  (let [#^HashMap m (:map pq)
	val (.get m item)] 
    (if (and val (<= (get-cost val) (get-cost cost)))
        :ignored
      (do (.put m item cost)
	  (sref-up! (:queue pq) conj [item cost])
	  :added)))) 

(deftest graph-queue-pq
  (let [pq (make-graph-queue-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) items)))
  (let [pq (make-graph-queue-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [-1 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) items)))
  (let [pq (make-graph-queue-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [4 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) (butlast items))))
  (let [pq (make-graph-queue-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [1 -1]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) (butlast items)))
    (pq-add! pq :a [1 -3])
    (is (= (pq-size pq) 0))
    (pq-add! pq :a [0 1])
    (is (= (pq-size pq) 1))
    )
    )




(derive ::StackPriorityQueue ::PriorityQueue)

(defn make-stack-pq 
  "A stack, which ignores priorities"
  [] {:class ::StackPriorityQueue :stack (sref nil)})

(defmethod pq-add! ::StackPriorityQueue [pq item cost]
  (sref-up! (:stack pq) conj [item cost])
  :added)

;(defmethod pq-add-all! ::StackPriorityQueue [pq items]
;  (let [old (sref-get (:stack pq))]
;    (sref-set! (:stack pq) (concat items old))
;    nil))

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

(deftest stack-pq 
  (let [pq (make-stack-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [2 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) (reverse items)))))


(derive ::GraphStackPriorityQueue ::StackPriorityQueue)

(defn make-graph-stack-pq
  "A stack that ignores priorities and repeated adds.  BEWARE of GHI with, e.g., depth-limited search."
  [] {:class ::GraphStackPriorityQueue :stack (sref nil) :map (new HashMap)})

(defmethod pq-add! ::GraphStackPriorityQueue [pq item cost]
  (let [#^HashMap m (:map pq)
	val (.get m item)] 
    (if (and val (<= (get-cost val) (get-cost cost)))
        :ignored
      (do (.put m item cost)
	  (sref-up! (:stack pq) conj [item cost])
	  :added))))

;(defmethod pq-add-all! ::GraphStackPriorityQueue [pq items]
;  (print " a ")
;  (let [#^HashMap m (:map pq);
;	old (sref-get (:stack pq))]
;    (sref-set! (:stack pq) 
;	       (concat (for [pair items :when (let [v (.get m (first pair))] 
;							   (or (nil? v) (< (second pair) v)))] 
;				    (do (.put m (first pair) (second pair)) pair))
;				  old))
;    (print " ae ")
;    nil))


(deftest graph-stack-pq
  (let [pq (make-graph-stack-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) (reverse items))))
  (let [pq (make-graph-stack-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [-1 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) (reverse items))))
  (let [pq (make-graph-stack-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [4 3]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) (reverse (butlast items)))))
  (let [pq (make-graph-stack-pq)
	items [[:a [1 2]] [:b [3 6]] [:c [2 3]] [:a [1 -1]]]]
    (pq-add-all! pq items)
    (is (= (pq-size pq) 3))
    (is (= (pq-remove-all! pq) (reverse (butlast items))))
    (pq-add! pq :a [1 -3])
    (is (= (pq-size pq) 0))
    (pq-add! pq :a [0 1])
    (is (= (pq-size pq) 1))
    ))




(derive ::TreePriorityQueue ::PriorityQueue)

(defn make-tree-search-pq 
  "Supports only add! and remove-min!, each item is added regardless of relation to previous objects" 
  [] {:class ::TreePriorityQueue :heap (new FibonacciHeapComp)})

(defmethod pq-add! ::TreePriorityQueue [pq item cost]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.insert heap item cost)
    :added))

(defmethod pq-peek-min ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.min heap)]
    [(.getData n) (.getKey n)]))

(defmethod pq-remove-min! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.removeMin heap)))

(defmethod pq-remove-min-with-cost! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.min heap) 
	c (.getKey n)]
    [(.removeMin heap) c]))

(defmethod pq-empty?  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.isEmpty heap)))

(defmethod pq-size  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.size heap)))

(defmethod pq-peek-pairs ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (for [#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node node (.nodeList heap)]
      [(.getData node) (.getKey node)])))
  
(deftest tree-search-pq 
  (let [pq (make-tree-search-pq)]
    (pq-add! pq :a 1)
    (pq-add! pq :a -1)
    (pq-add! pq :b 3)
    (pq-add! pq :b -3)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) [[:b -3] [:a -1] [:a 1] [:b 3]]))
    (pq-add! pq :a 10)
    (is (= (pq-remove-all! pq) [[:a 10]]))
    (pq-add! pq :a [1 2])
    (pq-add! pq :b [1 -1])
    (pq-add! pq :a [0 100])
    (pq-add! pq :b [1 3])
    (pq-add! pq :c [1 -10])
    (pq-add! pq :a [2 -100])
    (is (= (pq-remove-all! pq) [[:a [0 100]] [:c [1 -10]] [:b [1 -1]] [:a [1 2]] [:b [1 3]] [:a [2 -100]]]))))



(derive ::SafeTreePriorityQueue ::TreePriorityQueue)

(defn make-safe-tree-search-pq []
  (assoc (make-tree-search-pq) 
    :last-min (sref Double/NEGATIVE_INFINITY)
    :class ::SafeTreePriorityQueue))

(defmethod pq-remove-min! ::SafeTreePriorityQueue [pq] (first (pq-remove-min-with-cost! pq) ))

(defmethod pq-remove-min-with-cost! ::SafeTreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.min heap) 
	c (.getKey n)
	c-cost (get-cost c)]
    (assert-is (>= c-cost (sref-get (:last-min pq))))
    (sref-set! (:last-min pq) c-cost)
    [ (.removeMin heap) c]))


(deftest safe-tree-search-pq 
  (let [pq (make-safe-tree-search-pq)]
    (pq-add! pq :a 1)
    (pq-add! pq :a -1)
    (pq-add! pq :b 3)
    (pq-add! pq :b -3)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) [[:b -3] [:a -1] [:a 1] [:b 3]]))
    (pq-add! pq :a 10)
    (is (= (pq-remove-all! pq) [[:a 10]]))
    (pq-add! pq :a 10)
    (is (= (pq-remove-all! pq) [[:a 10]]))
    (pq-add! pq :a 9)
    (is (= (pq-size pq) 1))
    (is (thrown? Exception (pq-remove-min! pq))))
  (let [pq (make-safe-tree-search-pq)]
    (pq-add! pq :a [1 2])
    (pq-add! pq :b [1 -1])
    (pq-add! pq :a [0 100])
    (pq-add! pq :b [1 3])
    (pq-add! pq :c [1 -10])
    (pq-add! pq :a [2 -100])
    (is (= (pq-remove-all! pq) [[:a [0 100]] [:c [1 -10]] [:b [1 -1]] [:a [1 2]] [:b [1 3]] [:a [2 -100]]]))
    (pq-add! pq :a 1)
    (is (= (pq-size pq) 1))
    (is (thrown? Exception (pq-remove-min! pq)))))



(derive ::FancyTreePriorityQueue ::PriorityQueue)

(defn make-fancy-tree-search-pq 
  "Like tree PQ but supports removal, peeking, only allows one entry per identical item." 
  [] {:class ::FancyTreePriorityQueue :heap (new FibonacciHeapComp) :map (IdentityHashMap.)})

(defmethod pq-add! ::FancyTreePriorityQueue [pq item cost]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^IdentityHashMap       m    (:map pq)]
    (assert-is (not (.put m item (.insert heap item cost))))
    :added))

(defmethod pq-peek-min ::FancyTreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.min heap)]
    [(.getData n) (.getKey n)]))

(defmethod pq-remove! ::FancyTreePriorityQueue [pq item]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^IdentityHashMap       m    (:map pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.get m item)]
    (.delete heap n)
    (.remove m item)
    :removed))

(defmethod pq-remove-min-with-cost! ::FancyTreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^IdentityHashMap       m    (:map pq)
	#^com.bluemarsh.graphmaker.core.util.FibonacciHeapComp$Node n (.min heap)
	item (.removeMin heap)
	c (.getKey n)]
    (.remove m item)
    [item c]))

(defmethod pq-size  ::FancyTreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.size heap)))


(deftest fancy-tree-search-pq 
  (let [pq (make-fancy-tree-search-pq)]
    (pq-add! pq :a 1)
    (is (thrown? Exception (pq-add! pq :a 2))))
  (let [pq (make-fancy-tree-search-pq)]
    (pq-add-all! pq [[:a 1] [:b 0] [:c 2]])
    (is (= (pq-size pq) 3))
    (pq-remove! pq :b)
    (is (= (pq-remove-all! pq) [[:a 1] [:c 2]])))
  (let [pq (make-fancy-tree-search-pq)]
    (pq-add! pq 'a 1)
    (pq-add! pq 'a -1)
    (pq-add! pq 'b 3)
    (pq-add! pq 'b -3)
    (is (= (pq-size pq) 4))
    (is (= (pq-remove-all! pq) [['b -3] ['a -1] ['a 1] ['b 3]]))
    (pq-add! pq 'a 10)
    (is (= (pq-remove-all! pq) [['a 10]]))
    (pq-add! pq 'a 10)
    (is (= (pq-remove-all! pq) [['a 10]]))
    (pq-add! pq 'a 9)
    (is (= (pq-size pq) 1)))
  (let [pq (make-fancy-tree-search-pq)]
    (pq-add! pq 'a [1 2])
    (pq-add! pq 'b [1 -1])
    (pq-add! pq 'a [0 100])
    (pq-add! pq 'b [1 3])
    (pq-add! pq 'c [1 -10])
    (pq-add! pq 'a [2 -100])
    (is (= (pq-remove-all! pq) [['a [0 100]] ['c [1 -10]] ['b [1 -1]] ['a [1 2]] ['b [1 3]] ['a [2 -100]]]))
    (pq-add! pq 'a 1)
    (is (= (pq-size pq) 1))))





(derive ::GraphPriorityQueue ::PriorityQueue)

(defn make-graph-search-pq 
  "For graph search with consistent heuristic.  Remembers everything ever added, each removed at most once.  For most uses, a :re-added return value from add indicates an error.  Will take the better tiebreak of things on the open list, but ignores tiebreak for re-adding."
  [] {:class ::GraphPriorityQueue :map (new HashMap) :heap (new FibonacciHeapComp)})


(defmethod pq-add!  ::GraphPriorityQueue [pq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :re-added :decreased, or :ignored"
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert heap item cost)) :added)
	  (instance? FibonacciHeapComp$Node n)
	    (let [#^FibonacciHeapComp$Node n n] 
	      (if (>= (.compareTo #^Comparable cost (.getKey n)) 0) 
	           :ignored
		 (do (.decreaseKey heap n item cost)        :decreased)))
	  (number? n)          (if (< (get-cost cost) n)
				   (do (.put m item (.insert heap item cost)) :re-added)
				   ;(throw (IllegalArgumentException. "Heuristic inconsistency detected."))
				 :ignored)
	  :else                (throw (RuntimeException.) "Shouldn't happen."))))

(defn g-pq-add!  [pq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :re-added :decreased, or :ignored"
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert heap item cost)) :added)
	  (instance? FibonacciHeapComp$Node n)
	    (let [#^FibonacciHeapComp$Node n n] 
	      (if (>= (.compareTo #^Comparable cost (.getKey n)) 0) 
	           :ignored
		 (do (.decreaseKey heap n item cost)        :decreased)))
	  (number? n)          (if (< (get-cost cost) n)
				   (do (.put m item (.insert heap item cost)) :re-added)
				   ;(throw (IllegalArgumentException. "Heuristic inconsistency detected."))
				 :ignored)
	  :else                (throw (RuntimeException.) "Shouldn't happen."))))


(defmethod pq-replace!  ::GraphPriorityQueue [pq item cost]
  "Like pq-add!, but always replace the current value."
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	n (.get m item)]
    (if (or (nil? n) (number? n)) 
        (do (.put m item (.insert heap item cost)) :added)
      (do (pq-remove! pq item)
	  (pq-replace! pq item cost)
	  :replaced))))

(declare g-pq-remove!)
(defn g-pq-replace!  [pq item cost]
  "Like pq-add!, but always replace the current value."
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	n (.get m item)]
    (if (or (nil? n) (number? n)) 
        (do (.put m item (.insert heap item cost)) :added)
      (do (g-pq-remove! pq item)
	  (g-pq-replace! pq item cost)
	  :replaced))))

(defmethod pq-peek-min ::GraphPriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.min heap)]
    [(.getData n) (.getKey n)]))

(defn g-pq-peek-min [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.min heap)]
    [(.getData n) (.getKey n)]))

(defmethod pq-remove! ::GraphPriorityQueue [pq item]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.get m item)]
    (.delete heap n)
    (.put m item (get-cost (.getKey n)))
    :removed))

(defn g-pq-remove! [pq item]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.get m item)]
    (.delete heap n)
    (.put m item (get-cost (.getKey n)))
    (.getData n)))

(defmethod pq-remove-min! ::GraphPriorityQueue [pq]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.min heap) 
	c (.getKey n)
	ret (.removeMin heap)]
    (.put m ret (get-cost c))
    ret))

(defmethod pq-remove-min-with-cost! ::GraphPriorityQueue [pq]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.min heap) 
	c (.getKey n)
	ret (.removeMin heap)]
    (.put m ret (get-cost c))
    [ret c]))

(defn g-pq-remove-min-with-cost! [pq]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	#^FibonacciHeapComp$Node n (.min heap) 
	c (.getKey n)
	ret (.removeMin heap)]
    (.put m ret (get-cost c))
    [ret c]))

(defmethod pq-empty? ::GraphPriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.isEmpty heap)))

(defmethod pq-size ::GraphPriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.size heap)))

(defn g-pq-priority 
  "Return nil if the queue never had item, otherwise its priority (currently, or when removed)"
  [pq item]
  (let [#^HashMap m (:map pq) 
	#^FibonacciHeapComp heap (:heap pq)
	n (.get m item)]
    (cond (nil? n)                             nil
	  (instance? FibonacciHeapComp$Node n) (.getKey #^FibonacciHeapComp$Node n)
	  (number? n)                          n
	  :else                                (throw (RuntimeException.) "Shouldn't happen."))))



(deftest graph-search-pq 
  (let [pq (make-graph-search-pq) ; simple tests, integer costs
	a1 (with-meta 'a {:a1 true})
	a2 (with-meta 'a {:a2 true})
	a3 (with-meta 'a {:a3 true})]
    (is (= :added (pq-add! pq a1 1)))
    (is (= :ignored (pq-add! pq a2 2)))
    (is (identical? (first (pq-peek-min pq)) a1))
    (is (= :decreased (pq-add! pq a3 0)))
    (is (= (pq-size pq) 1))
    (let [[r c] (pq-remove-min-with-cost! pq)]
      (is (identical? r a3))
      (is (= c 0))
      (is (= (meta r) {:a3 true})))
    (is (= :ignored (pq-add! pq a2 0)))
    (is (= (pq-size pq) 0))
    (is (= :re-added (pq-add! pq a2 -1)))
    (is (= (pq-size pq) 1))
    (let [[r c] (pq-remove-min-with-cost! pq)]
      (is (identical? r a2))
      (is (= c -1))
      (is (= (meta r) {:a2 true}))))
  (let [pq (make-graph-search-pq) ; with tiebreaking ...
	a1 (with-meta 'a {:a1 true})
	a2 (with-meta 'a {:a2 true})
	a3 (with-meta 'a {:a3 true})]
    (is (= :added (pq-add! pq a1 [1 2] )))
    (is (= :ignored (pq-add! pq a2 [2 3])))
    (is (= :ignored (pq-add! pq a2 [1 2])))
    (is (identical? (first (pq-peek-min pq)) a1))
    (is (= :decreased (pq-add! pq a3 [1 1])))
    (is (= :added (pq-add! pq 'b [1 3] )))
    (is (= :decreased (pq-add! pq 'b [1 -1] )))
    (is (= :added (pq-add! pq 'c [3 -10] )))
    (is (= :decreased (pq-add! pq 'c [0 10] )))
    (is (= (pq-remove-all! pq) [['c [0 10]] ['b [1 -1]] ['a [1 1]]]))
    (is (= :ignored (pq-add! pq 'c [1 0])))
    (is (= :ignored (pq-add! pq 'c [0 0])))
    (is (= :re-added (pq-add! pq 'c [-1 100])))
    (is (= (pq-size pq) 1))))




(derive ::UnionPriorityQueue ::PriorityQueue)

(defn make-union-pq 
  "Union view of two priority queues -- only supports peek, size, and min removal." 
  [& queues] 
  {:class ::UnionPriorityQueue :queues queues})

(defmethod pq-add! ::UnionPriorityQueue [pq item cost]
  (throw (UnsupportedOperationException.)))

(defmethod pq-peek-min ::UnionPriorityQueue [pq]
  (first-maximal-element (comp - second) (map pq-peek-min (remove pq-empty? (:queues pq)))))

(defmethod pq-remove! ::UnionPriorityQueue [pq item]
  (throw (UnsupportedOperationException.)))

(defmethod pq-remove-min-with-cost! ::UnionPriorityQueue [pq]
  (pq-remove-min-with-cost!
    (first-maximal-element #(- (second (pq-peek-min %))) (remove pq-empty? (:queues pq)))))

(defmethod pq-size  ::UnionPriorityQueue [pq]
  (apply + (map pq-size (:queues pq))))


(deftest union-pq 
  (let [q1 (make-fancy-tree-search-pq)
        q2 (make-fancy-tree-search-pq)
        pq (make-union-pq q1 q2)]
    (pq-add! q1 :a 1)
    (pq-add! q2 :b 2)
    (pq-add! q1 :c 3)
    (pq-add! q2 :d 4)
    (pq-add! q1 :e 5)
    (is (= (pq-peek-min pq) [:a 1]))
    (is (= (pq-size pq) 5))
    (is (= (pq-remove-all! pq) [[:a 1] [:b 2] [:c 3] [:d 4] [:e 5]]))))




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
  (new FibonacciHeapComp))

(defn simple-pq-add! [#^FibonacciHeapComp pq item cost]
  (.insert pq item cost))

(defn simple-pq-remove-min! [#^FibonacciHeapComp pq]
  (.removeMin pq))

(defn simple-pq-remove-min-with-cost! [#^FibonacciHeapComp pq]
  (let [#^FibonacciHeapComp$Node n (.min pq) 
	c (.getKey n)]
    (vector (.removeMin pq) c)))

(defn simple-pq-size [#^FibonacciHeapComp pq]
  (.size pq))

(defn simple-pq-empty? [#^FibonacciHeapComp pq]
  (.isEmpty pq))




(defn make-fancy-priority-queue []
  "A slightly slower mutable priority queue that only allows for single instance of each object, maintaining min priority."
  (vector (new HashMap) (new FibonacciHeapComp)))

(defn fancy-pq-add! [[#^HashMap m #^FibonacciHeapComp pq] item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^FibonacciHeapComp$Node n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert pq item cost)) :added)
	  (< cost (.getKey n)) (do (.decreaseKey pq n item cost)        :decreased)
	  true                 :ignored)))

(defn fancy-pq-remove! [[#^HashMap m #^FibonacciHeapComp pq] item]
  (let [#^FibonacciHeapComp$Node n (.get m item)]
    (.delete pq n)))

(defn fancy-pq-remove-min! [[#^HashMap m #^FibonacciHeapComp pq]]
  (let [ret (.removeMin pq)]
    (.remove m ret)
    ret))

(defn fancy-pq-remove-min-with-cost! [[#^HashMap m #^FibonacciHeapComp pq]]
  (let [#^FibonacciHeapComp$Node n (.min pq) 
	c (.getKey n)
	ret (.removeMin pq)]
    (.remove m ret)
    (vector ret c)))

(defn fancy-pq-size [[#^HashMap m #^FibonacciHeapComp pq]]
  (.size pq))

(defn fancy-pq-empty? [[#^HashMap m #^FibonacciHeapComp pq]]
  (.isEmpty pq))

(defn fancy-pq-contains? [[#^HashMap m #^FibonacciHeapComp pq] item]
  (.containsKey m item))





(defn make-simple-pq [] {:class ::TreePriorityQueue :heap (new FibonacciHeapComp)})
(defn make-fancy-pq [] {:class ::GraphPriorityQueue :map (new HashMap) :heap (new FibonacciHeapComp)})

(defmulti pq-add! (fn [a b c] (:class a)))
(defmulti pq-remove-min! :class)
(defmulti pq-empty? :class)


(defmethod pq-add! ::TreePriorityQueue [pq item cost]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.insert heap item cost)))

(defmethod pq-remove-min! ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.removeMin heap)))

(defmethod pq-empty?  ::TreePriorityQueue [pq]
  (let [#^FibonacciHeapComp heap (:heap pq)]
    (.isEmpty heap)))


(defmethod pq-add!  ::GraphPriorityQueue [fpq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :decreased, or :ignored"
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeapComp pq (:heap fpq)
	#^FibonacciHeapComp$Node n (.get m item)]
    (cond (nil? n)             (do (.put m item (.insert pq item cost)) :added)
	  (< cost (.getKey n)) (do (.decreaseKey pq n item cost)        :decreased)
	  true                 :ignored)))

(defmethod pq-remove-min! ::GraphPriorityQueue [fpq]
  (let [#^HashMap m (:map fpq) 
	#^FibonacciHeapComp pq (:heap fpq)
	ret (.removeMin pq)]
    (.remove m ret)
    ret))

(defmethod pq-empty? ::GraphPriorityQueue [fpq]
  (let [#^FibonacciHeapComp pq (:heap fpq)]
    (.isEmpty pq)))


 ; Fairly comparable times.  Must wrap either with HaspMap to make usable. (FibHeap slightly slower w/o decreasekeys)
 ; Declaring types makes huge difference (factor of 6!)  (dotimes [_ 3]
    (time (let [#^PriorityQueue pq (new PriorityQueue)]
	    (dotimes [_ 1000000] 
	      (.add pq (rand-int 1000000)))
	    (while (not (.isEmpty pq)) (.poll pq))))
    (time (let [#^FibonacciHeapComp pq (new FibonacciHeapComp)]
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

