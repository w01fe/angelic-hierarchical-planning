(ns edu.berkeley.ai.domains.warehouse
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips])
 )


(let [f (util/path-local "warehouse.pddl")]
  (defn make-warehouse-strips-domain []
    (strips/read-strips-planning-domain f)))
 

; initial-stacks is map from column number to stacks of block names (top-down).
; goal-stacks is seq of desired stacks
(defn make-warehouse-strips-env [width height initial-pos initial-faceright? initial-stacks initial-holding goal-stacks]
  (strips/make-strips-planning-instance 
   "nav-switch"
   (make-warehouse-strips-domain)
   {'xc (map #(util/symbol-cat "x" %) (range width))
    'yc (map #(util/symbol-cat "y" %) (range height))
    'block (apply concat 
		  (map #(util/symbol-cat "table" %) (range width))
		  (vals initial-stacks))}
   (concat (if initial-holding '[[holding initial-holding]] '[[gripperempty]])
	   (when initial-faceright? '[[facingright]])
	   [['gripperat (util/symbol-cat "x" (first initial-pos)) (util/symbol-cat "y" (second initial-pos))]]
	   (map (fn [x] ['leftof (util/symbol-cat "x" (dec x)) (util/symbol-cat "x" x)]) (range 1 width))
	   (map (fn [x] ['above   (util/symbol-cat "y" x) (util/symbol-cat "y" (dec x))]) (range 1 height))
	   [['topy (util/symbol-cat "y" (dec height))]]
	   (util/forcat [x (range width)]
	     (let [stack (concat (get initial-stacks x) [(util/symbol-cat "table" x)])]
	       (concat [['clear (first stack)]]
		       (for [[b c] (partition 2 1 stack)]
			 ['on b c])
		       (util/forcat [[y b] (util/indexed (reverse stack))]
			 (do 
			   (util/assert-is (not (= initial-pos [x y])))
			   [['blockat b (util/symbol-cat "x" x) (util/symbol-cat "y" y)]
			    ['someblockat (util/symbol-cat "x" x) (util/symbol-cat "y" y)]]))))))
   (for [goal-stack goal-stacks
	 [b c] (partition 2 1 goal-stack)]
     ['on b c])
   (fn [state]
;     (println state)
     (let [pos (map #(util/desymbolize % 1) (strips/get-strips-state-pred-val state 'gripperat))
	   holding (if (contains? state '[gripperempty]) nil (first (strips/get-strips-state-pred-val state 'holding)))
	   facingright? (contains? state '[facingright])
	   square-map (assoc (into {} (filter identity (for [c state] 
							(when (= (first c) 'blockat) 
							  [(map #(util/desymbolize % 1) [(nth c 2) (nth c 3)])
							   (.toUpperCase (name (nth c 1)))]))))
			pos (if holding (.toLowerCase (name holding)) "#"))]
;       (println pos holding facingright? square-map)
       (util/str-join "\n"
	 (for [y (reverse (range 1 height))]
	   (apply str
	     (for [x (range width)]
	       (get square-map [x y] (if facingright? ">" "<"))))))))))

(def *warehouse-hierarchy-unguided* "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08_unguided.hierarchy")


(defn- get-and-check-sol [env graph?]
  (map :name
    (first
     (envs/check-solution env
       ((if graph? 
	  edu.berkeley.ai.search.algorithms.textbook/a-star-graph-search 
	  edu.berkeley.ai.search.algorithms.textbook/a-star-search)
	(edu.berkeley.ai.search/make-initial-state-space-node 
	 env   
	 (constantly 0)))))))

(util/deftest flat-warehouse
  (util/testing "tiny instance"
    (let [env (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]])]
      (doseq [graph? [true false]
	      simplifier [identity strips/constant-predicate-simplify
			  (comp strips/flatten-strips-instance strips/constant-predicate-simplify)]]
	(util/is (= '((get-l a table0 x0 x1 y1) (left x1 x0 y1) (turn-r x0 y1) (put-r a table1 x1 x0 y0 y1))
		    (get-and-check-sol (simplifier env) graph?))))))
  (util/testing "bigger instance"
    (let [env (make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]])]
      (doseq [simplifier [strips/constant-predicate-simplify
			  (comp strips/flatten-strips-instance strips/constant-predicate-simplify)]]
	(util/is (= 14 
		    (count (get-and-check-sol (simplifier env) true))))))))




(comment 
  (u util domains.strips domains.warehouse envs search search.algorithms.textbook)
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

  )





