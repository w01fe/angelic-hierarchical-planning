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
(defn make-warehouse-strips-env [height width initial-pos initial-faceright? initial-stacks initial-holding goal-stacks]
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
   str))





