(ns exp.warehouse
 (:import [java.util HashSet HashMap])
 (:require [edu.berkeley.ai [util :as util]] 
           [exp [env :as env] [hierarchy :as hierarchy]]))

; Note: WW heuristic is inconsistent.

(defn- make-dir [s name [dx dy]]
  (let [[cx cy :as cp] (env/get-var s '[at])
        [w h]          (get (env/get-var s :const) '[topright])
        nx (+ cx dx), ny (+ dy dy)]
    (when (and (<= 1 nx w) (<= 1 ny h))
      (env/FactoredPrimitive
       name
       {['at] cp ['someblockat nx ny] false}
       {['at] [nx ny]}
       -1))))

(defn- make-left  [s] (make-dir '[left]  [-1 0 ]))
(defn- make-right [s] (make-dir '[right] [ 1 0 ]))
(defn- make-down  [s] (make-dir '[down]  [ 0 -1]))
(defn- make-up    [s] (make-dir '[up]    [ 0  1]))


(defn- make-turn   [s]
  (let [[cx cy] (env/get-var s '[at])
        cur-fr  (env/get-var s '[facingright])]
    (when (= cy (nth (get (env/get-var s :const) '[topright]) 1))  
      (env/FactoredPrimitive [(if cur-fr 'turn-l 'turn-r)] {['at] [cx cy] ['facingright] cur-fr} 
                             {'facingright (not cur-fr)} -1))))

(defn- make-get [s]
  (when-not (env/get-var s ['holding])
    (let [[cx cy] (env/get-var s '[at])
          cur-fr  (env/get-var s '[facingright])
          [width] (get (env/get-var s :const) '[topright])
          bx      (+ cx (if cur-fr 1 -1))]
      (when-let [b (and (<= bx 1 width) (env/get-var s ['blockat bx cy]))]
        (when-not (env/get-var s ['on b])
          (let [c (env/get-var s ['blockat bx (dec cy)])]
            (env/FactoredPrimitive
             [(if cur-fr 'get-r 'get-l) b c]
             {['at] [cx cy] ['facingright] cur-fr ['blockat bx cy] b 
              ['on c] b ['on b] nil ['holding] nil}
             {['blockat bx cy] nil ['on c] nil ['someblockat bx cy] false ['holding] b}
             -1)))))))

(defn- make-put [s]
  (when-let [b (env/get-var s ['holding])]
    (let [[cx cy] (env/get-var s '[at])
          cur-fr  (env/get-var s '[facingright])
          [width] (get (env/get-var s :const) '[topright])
          bx      (+ cx (if cur-fr 1 -1))]
      (when-let [c (and (<= bx 1 width) (env/get-var s ['blockat bx (dec cy)]))]
        (when-not (env/get-var s ['on c])
          (env/FactoredPrimitive
           [(if cur-fr 'put-r 'put-l) b c]
           {['at] [cx cy] ['facingright] cur-fr ['blockat bx (dec cy)] c 
            ['on c] nil ['holding] b}
           {['blockat bx cy] b ['on c] b ['someblockat bx cy] true ['holding] nil}
           -1))))))



(deftype WarehouseEnv [init goal] :as this
 env/Env
  (initial-state [] init)
  (actions-fn []
   (fn warehouse-actions [s]
     (for [f [make-left make-right make-up make-down make-turn make-get make-put]
           :let [a (f s)] :when a]
       a)))
  (goal-fn [] #(when (env/state-matches-map? % goal) (env/solution-and-reward %)))
 env/FactoredEnv
  (goal-map [] goal))


; initial-stacks is map from column number to stacks of block names (top-down).
; goal-stacks is seq of desired stacks
(defn make-warehouse-env 
  [width height initial-pos initial-faceright? initial-stacks initial-holding goal-stacks]
  (let [bottomleft [1 1]
        topright   [width height]
        blocks     (set (util/cons-when initial-holding (apply concat (vals initial-stacks))))
        tables     (set (for [i (range 1 (inc height))] (util/symbol-cat 'table i)))]
    (assert (not (contains? blocks nil)))
    (assert (empty? (clojure.set/intersection tables blocks)))
    (assert (every? identity (map <= [1 1] initial-pos topright)))
    (assert (every? #(<= 1 % width) (keys initial-stacks)))
    (assert (every? #(< (count %) (dec height)) (vals initial-stacks)))
    (assert (every? (into blocks tables) (apply concat goal-stacks)))
    (assert (every? #(= (count % 2)) goal-stacks))
    (assert (< (count (get initial-stacks (first initial-pos))) (second initial-pos)))
    (let [stacks (for [i (range 1 (inc width))] 
                   (take height (concat [(util/symbol-cat 'table i)] 
                                        (reverse (get initial-stacks i)) 
                                        (repeat nil))))]
      (WarehouseEnv 
       (into {:const {['topright] topright}
              '[at]  (vec initial-pos)
              '[facingright] (if initial-faceright? true false)
              '[holding]     (or initial-holding nil)}
             (apply concat    
                    (for [[x stack] (util/indexed stacks)
                          [y block] (util/indexed stack)]
                      (util/cons-when
                       (when block ['on block] (or (get stack (inc y)) nil))
                       [['blockat x y] (or block nil)]
                       [['someblockat x y] (if block true false)]))))
       (into {} (for [stack goal-stacks, [a b] (partition 2 1 stack)] [['on b] a]))))))





(comment 
  (u util envs.strips domains.warehouse envs search search.algorithms.textbook)
  (time (map :name (first (a-star-search (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])) (constantly 0))))))
  (time (map :name (first (a-star-search (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[a b]])) (constantly 0))))))
  (time (map :name (first (a-star-search (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]])) (constantly 0))))))
  (time (map :name (first (a-star-graph-search (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 3 4 [1 2] true {0 '[b a] 2 '[c]} nil ['[a b c]])) (constantly 0))))))
  (time (map :name (first (a-star-graph-search (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]])) (constantly 0))))))


  (let [node (make-initial-state-space-node (constant-predicate-simplify (make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[ b a]])) (constantly 0))]
    (time (map :name (first (a-star-search node)))))

  (let [env (constant-predicate-simplify
	     (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))]
    (println 
     (str-join "\n\n"
     (map #(state-str env %)
       (nth
        (check-solution env
	  (a-star-graph-search (make-initial-state-space-node env (constantly 0)))) 2)))))

  (parse-hierarchy "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse.hierarchy" (make-warehouse-strips-domain))

  (time (map :name (first (a-star-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))))))))

  )


