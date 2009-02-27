(ns edu.berkeley.ai.domains.warehouse
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips]
	   [edu.berkeley.ai.angelic :as angelic]
	   [edu.berkeley.ai.angelic.dnf-simple-valuations :as dsv])
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
(def *warehouse-hierarchy* "/Users/jawolfe/projects/angel/src/edu/berkeley/ai/domains/warehouse_icaps08.hierarchy")


; Act description used in hierarchy


(derive ::WarehouseActDescriptionSchema ::angelic/PropositionalDescription)

(defmethod angelic/parse-description :warehouse-act [desc domain params]
  {:class ::WarehouseActDescriptionSchema})


(derive ::WarehouseActDescription ::angelic/PropositionalDescription)
(defstruct warehouse-act-description :class :fn)
(defn make-warehouse-act-description [fn] (struct warehouse-act-description ::WarehouseActDescription fn))


(import '[java.util HashSet HashMap])

(defn- manhattan [p1 p2]
  (+ (util/abs (- (first p1) (first p2)))
     (util/abs (- (second p1) (second p2)))))
;  (+ (util/symbol-abs-diff (first p1) (first p2) 1)
;     (util/symbol-abs-diff (second p1) (second p2) 1)))

(defn- parse-pos [[x y]]
  [(util/desymbolize x 1) (util/desymbolize y 1)])

(defn- extract-positions [dnf]
  (let [gripper-pos (HashSet.)
	block-pos   (HashMap.)
	holding     (util/sref nil)]
    (doseq [clause dnf
	    [atom] clause]
      (let [pred (first atom)]
       (cond (= pred 'gripperat) (.add gripper-pos (parse-pos (next atom)))
 	     (= pred 'blockat)   
	      (let [block (second atom)
		    pos   (parse-pos (next (next atom)))
		    prev-pos (.get block-pos block)]
		(if prev-pos
		    (util/assert-is (= prev-pos pos))
		  (.put block-pos block pos)))
	     (= pred 'holding)
	      (let [block (second atom)
		    old-holding (util/sref-get holding)]
		(if old-holding
		    (util/assert-is (= old-holding block))
		  (util/sref-set! holding block))))))
    (when-let [b (util/sref-get holding)]
      (throw (IllegalArgumentException.)) 
      (let [positions (seq gripper-pos)]
	(util/assert-is (= (count positions) 1))
        (.put block-pos b (first positions))))
;    (println dnf)
    (util/assert-is (not (.isEmpty gripper-pos)))
 ;   (println gripper-pos)
    [gripper-pos block-pos]))

(defn- make-simpler-heuristic [table-pos-map floating-chains]
  (fn [dnf]
;    (println "simple")
    (let [[#^HashSet gripper-pos, #^HashMap block-pos] (extract-positions dnf)]
;      (if (.isEmpty gripper-pos) Double/NEGATIVE_INFINITY
   ;   (println "Going: ")
      (- 0 
	 (reduce + (for [[b p] table-pos-map] (manhattan p (.get block-pos b))))
	 (reduce + (for [chain floating-chains]
		    (let [positions (map #(.get block-pos %) chain)
			  medx      (util/median (map first positions))]
		      (+ (loop [positions positions vert (int 0)]
			   (if (next positions)
			       (recur (next positions) (+ vert (Math/abs (int (- (second (first positions))
										 (inc (second (fnext positions))))))))
			     vert))
			 (reduce + 
			   (for [pos positions]
			     (util/abs (- (first pos) medx))))))))))))


(defn- make-matching-based-heuristic [table-pos-map chains]
  (let [term (gensym "term")
	block-set (set (apply concat chains))]
    (fn [dnf]
;      (println "matching")
      (let [[#^HashSet gripper-pos, #^HashMap block-pos] (extract-positions dnf)]
;	(if (.isEmpty gripper-pos) Double/NEGATIVE_INFINITY
        (- 
	 ; Matching
	 (let [positions (seq (remove (fn [[b c g]] (= c g)) 
			    (map #(vector % (.get block-pos %) (get table-pos-map %)) block-set)))
	       blocks    (cons term (map first positions))]
	   (if positions
 	    (util/maximum-matching blocks blocks
;	    (util/prln	     
             (concat
	      (for [[b c g] positions] ; Get to first block and pick it up
		[term b (- (util/reduce-key min #(max 1 (manhattan % c)) gripper-pos))])   ;TODO: if holding??
	      (for [[b c g] positions] ; Put final block in final position (could have max 2?)
		[b term (- (manhattan c g))])
	      (for [[b1 c1 g1] positions, ; Holding b1; put it in g1, go to b1, pick it up
		    [b2 c2 g2] positions]  ; TODO: disallow [b b ...? ]
		[b1 b2 (- (max 1 (+ (manhattan c1 g1) (manhattan g1 c2))))])));)
	    0))

  	 ; Count switches
	  (* 4 (util/sum-over 
	       (fn [chain]
		 (let [positions (map #(vector (.get block-pos %) (get table-pos-map %)) chain)]
		   (util/assert-is (not (empty? positions)))
		   (util/count-when
		    (fn [rest-pos]
;		      (println rest-pos)
		      (let [[cur-pos goal-pos] (first rest-pos)]
			(some 
			  (fn [[cur-pos2 goal-pos2]]
			    (util/assert-is (> (second goal-pos) (second goal-pos2)))
			    (and (not (= cur-pos2 goal-pos2))
				 (> (second cur-pos) (second cur-pos2))))
			  (next rest-pos))))
		    (util/iterate-while next (seq positions)))))
	       chains)))))))




(defmethod angelic/instantiate-description-schema ::WarehouseActDescriptionSchema [desc instance]
  (let [goal-atoms (util/safe-get instance :goal-atoms)]
    (doseq [atom goal-atoms] (util/assert-is (= (first atom) 'on)))
    (let [on-map     (into {} (map #(subvec % 1) goal-atoms))
	  top-blocks (util/difference (set (keys on-map)) (set (vals on-map)))
	  chains     (map (fn [t] (util/iterate-while #(get on-map %) t)) top-blocks)
	  [table-chains floating-chains] (util/separate #(.startsWith #^String (name (last %)) "table") chains)
	  table-pos-map (into {} 
			  (apply concat
			    (for [chain table-chains]
			      (let [x (Integer/parseInt (.substring #^String (name (last chain)) 5))]
				(for [[block y] (next (map vector (reverse chain) (iterate inc 0)))]
				  [block [x y]])))))]
      (println "CREATE ACT" chains floating-chains table-pos-map)
      (make-warehouse-act-description
       (if (empty? floating-chains)
	   (make-matching-based-heuristic table-pos-map (map butlast chains))
	 (make-simpler-heuristic table-pos-map floating-chains))))))
;      (println table-pos-map floating-chains))))
	  

(defmethod angelic/ground-description ::WarehouseActDescription [desc var-map] desc)
  

(defmethod angelic/progress-optimistic [::angelic/PessimalValuation ::WarehouseActDescription] [val desc]  val)

(defmethod angelic/progress-optimistic [::dsv/DNFSimpleValuation ::WarehouseActDescription] [val desc]
  (angelic/make-conditional-valuation 
   envs/*true-condition*
   (+ (angelic/get-valuation-upper-bound val) ((:fn desc) (util/safe-get val :dnf)))))

(defmethod angelic/progress-pessimistic [::angelic/Valuation ::WarehouseActDescription] [val desc]
  (throw (UnsupportedOperationException.)))








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

  (time (map :name (first (a-star-search (alt-node (get-hierarchy *warehouse-hierarchy* (constant-predicate-simplify (make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))))))))

  )


