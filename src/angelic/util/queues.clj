(ns angelic.util.queues
  (:import [java.util HashMap IdentityHashMap]) 
  (:use angelic.util clojure.test)
  (:require [w01fe.fibonacci-heap.core :as fib]))


;; Priority queues. 
;; cost can be any Comparable object, to enable tiebreaking.  For the fancier queues that keep track of 
;; a "best" cost, the get-cost method will be called to get the actual cost from the object.
;; By default, this is the number itself for a number, or the first element of a vector.

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
  (let [^HashMap m (:map pq)
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
  (let [^HashMap m (:map pq)
	val (.get m item)] 
    (if (and val (<= (get-cost val) (get-cost cost)))
        :ignored
      (do (.put m item cost)
	  (sref-up! (:stack pq) conj [item cost])
	  :added))))

;(defmethod pq-add-all! ::GraphStackPriorityQueue [pq items]
;  (print " a ")
;  (let [^HashMap m (:map pq);
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


(defn flip [[x y]] [y x])


(derive ::TreePriorityQueue ::PriorityQueue)

(defn make-tree-search-pq 
  "Supports only add! and remove-min!, each item is added regardless of relation to previous objects" 
  [] {:class ::TreePriorityQueue :heap (fib/fibonacci-heap)})

(defmethod pq-add! ::TreePriorityQueue [pq item cost]
  (fib/add! (:heap pq) cost item)
  :added)

(defmethod pq-peek-min ::TreePriorityQueue [pq]
  (-> pq :heap fib/peek-min flip))

(defmethod pq-remove-min! ::TreePriorityQueue [pq]
  (-> pq :heap fib/remove-min! second))

(defmethod pq-remove-min-with-cost! ::TreePriorityQueue [pq]
  (-> pq :heap fib/remove-min! flip))

(defmethod pq-empty?  ::TreePriorityQueue [pq]
  (-> pq :heap fib/empty?))

(defmethod pq-size  ::TreePriorityQueue [pq]
  (-> pq :heap count))

(defmethod pq-peek-pairs ::TreePriorityQueue [pq]
  (map flip (-> pq :heap fib/peek-seq)))
  
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
  (let [[c data] (-> pq :heap fib/remove-min!)
	c-cost (get-cost c)]
    (assert (>= c-cost (sref-get (:last-min pq))))
    (sref-set! (:last-min pq) c-cost)
    [data c]))


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
    (is (thrown? AssertionError (pq-remove-min! pq))))
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
    (is (thrown? AssertionError (pq-remove-min! pq)))))



(derive ::FancyTreePriorityQueue ::PriorityQueue)

(defn make-fancy-tree-search-pq 
  "Like tree PQ but supports removal, peeking, only allows one entry per identical item." 
  [] {:class ::FancyTreePriorityQueue :heap (fib/fibonacci-heap) :map (IdentityHashMap.)})

(defmethod pq-add! ::FancyTreePriorityQueue [pq item cost]
  (let [^IdentityHashMap       m    (:map pq)]
    (assert (not (.put m item (-> pq :heap (fib/add! cost item)))))
    :added))

(defmethod pq-peek-min ::FancyTreePriorityQueue [pq]
  (-> pq :heap fib/peek-min flip))

(defmethod pq-remove! ::FancyTreePriorityQueue [pq item]
  (let [^IdentityHashMap       m    (:map pq)]
    (-> pq :heap (fib/remove! (.get m item)))
    (.remove m item)
    :removed))

(defmethod pq-remove-min-with-cost! ::FancyTreePriorityQueue [pq]
  (let [[c item] (-> pq :heap fib/remove-min!)
	^IdentityHashMap       m    (:map pq)]
    (.remove m item)
    [item c]))

(defmethod pq-size  ::FancyTreePriorityQueue [pq]
  (-> pq :heap count))


(deftest fancy-tree-search-pq 
  (let [pq (make-fancy-tree-search-pq)]
    (pq-add! pq :a 1)
    (is (thrown? AssertionError (pq-add! pq :a 2))))
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



;; Methods were provided as functions  here because multimethod dispatch was too inefficient.
;; (this may have changed over the years)

(derive ::GraphPriorityQueue ::PriorityQueue)

(defn make-graph-search-pq 
  "For graph search with consistent heuristic.  Remembers everything ever added, each removed at most once.  For most uses, a :re-added return value from add indicates an error.  Will take the better tiebreak of things on the open list, but ignores tiebreak for re-adding."
  [] {:class ::GraphPriorityQueue :map (new HashMap) :heap (fib/fibonacci-heap)})


(defn g-pq-add! [pq item cost]
  "Add or decrease key for item as appropriate.  Returns :added, :re-added :decreased, or :ignored"
  (let [^HashMap m (:map pq) 
	heap (:heap pq)
	n (.get m item)]
    (cond (nil? n)             (do (.put m item (fib/add! heap cost item)) :added)
	  (fib/node? n)
            (if (>= (.compareTo ^Comparable cost (fib/node-key n)) 0) 
              :ignored
              (do (fib/decrease-key! heap n cost item)        :decreased))
	  (number? n)          (if (< (get-cost cost) n)
				   (do (.put m item (fib/add! heap cost item)) :re-added)
				   ;(throw (IllegalArgumentException. "Heuristic inconsistency detected."))
				 :ignored)
	  :else                (throw (RuntimeException.) "Shouldn't happen."))))

(defmethod pq-add!  ::GraphPriorityQueue [pq item cost]
  (g-pq-add! pq item cost))


(defn g-pq-add-all! [pq items]
  (doseq [[i c] items] (g-pq-add! pq i c)))


(declare g-pq-remove!)
(defn g-pq-replace!  [pq item cost]
  "Like pq-add!, but always replace the current value."
  (let [^HashMap m (:map pq) 
	heap (:heap pq)
	n (.get m item)]
    (if (or (nil? n) (number? n)) 
        (do (.put m item (fib/add! heap cost item)) :added)
      (do (g-pq-remove! pq item)
	  (g-pq-replace! pq item cost)
	  :replaced))))

(defmethod pq-replace!  ::GraphPriorityQueue [pq item cost]
  (g-pq-replace! pq item cost))


(defn g-pq-peek-min [pq]
  (-> pq :heap fib/peek-min flip))

(defmethod pq-peek-min ::GraphPriorityQueue [pq]
  (g-pq-peek-min pq))


(defn g-pq-remove! [pq item]
  (let [^HashMap m (:map pq) 
        n (.get m item)]
    (fib/remove! (:heap pq) n)
    (.put m item (get-cost (fib/node-key n)))
    (fib/node-val n)))

(defmethod pq-remove! ::GraphPriorityQueue [pq item]
  (g-pq-remove! pq item)
  :removed)


(defmethod pq-remove-min! ::GraphPriorityQueue [pq]
  (let [^HashMap m (:map pq)
        [c ret] (fib/remove-min! (:heap pq))]
    (.put m ret (get-cost c))
    ret))

(defn g-pq-remove-min-with-cost! [pq]
  (let [^HashMap m (:map pq)
        [c ret] (fib/remove-min! (:heap pq))]
    (.put m ret (get-cost c))
    [ret c]))

(defmethod pq-remove-min-with-cost! ::GraphPriorityQueue [pq]
  (g-pq-remove-min-with-cost! pq))

(defn g-pq-empty? [pq]
  (-> pq :heap fib/empty?))

(defmethod pq-empty? ::GraphPriorityQueue [pq]
  (g-pq-empty? pq))



(defmethod pq-size ::GraphPriorityQueue [pq]
  (-> pq :heap count))

(defn g-pq-priority 
  "Return nil if the queue never had item, otherwise its priority (currently, or when removed)"
  [pq item]
  (let [^HashMap m (:map pq) 
	n (.get m item)]
    (cond (nil? n)      nil
	  (fib/node? n) (fib/node-key n)
	  (number? n)   n
	  :else         (throw (RuntimeException.) "Shouldn't happen."))))


(defmethod pq-peek-pairs ::GraphPriorityQueue [pq]
  (map flip (-> pq :heap fib/peek-seq)))


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

(defn first-minimal-element-comp [key-fn coll]
  (assert (seq coll))
  (loop [best (first coll) bk (key-fn best) coll (next coll)]
    (if (empty? coll) best
      (let [[f & r] coll
            k       (key-fn f)]
        (if (neg? (compare k bk))
            (recur f k r)
          (recur best bk r))))))


(derive ::UnionPriorityQueue ::PriorityQueue)

(defn make-union-pq 
  "Union view of two priority queues -- only supports peek, size, and min removal." 
  [& queues] 
  {:class ::UnionPriorityQueue :queues queues})

(defmethod pq-add! ::UnionPriorityQueue [pq item cost]
  (throw (UnsupportedOperationException.)))

(defmethod pq-peek-min ::UnionPriorityQueue [pq]
  (first-minimal-element-comp second (map pq-peek-min (remove pq-empty? (:queues pq)))))

(defmethod pq-remove! ::UnionPriorityQueue [pq item]
  (throw (UnsupportedOperationException.)))

(defmethod pq-remove-min-with-cost! ::UnionPriorityQueue [pq]
  (pq-remove-min-with-cost!
    (first-minimal-element-comp #(second (pq-peek-min %)) (remove pq-empty? (:queues pq)))))

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








