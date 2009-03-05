(ns edu.berkeley.ai.domains.hybrid-blocks
 (:import [java.util HashMap HashSet])
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.hybrid-strips :as hs])
 )



(let [f (util/path-local "hybrid_blocks.pddl")]
  (defn make-hybrid-blocks-strips-domain []
    (hs/read-hybrid-strips-planning-domain f)))
 
(declare process-block-tree)
(defn- process-block-forest [stacks on-block on-lx on-rx on-ty max-h gripper-pos #^HashSet block-set #^HashSet on-set #^HashMap num-map]
  (loop [li [0 0], stacks (seq stacks)]
    (when stacks
      (let [ni (process-block-tree (first stacks) on-block on-lx on-rx on-ty max-h gripper-pos block-set on-set num-map)]
	(util/assert-is (<= (second li) (first ni)))
	(util/assert-is (<= (second ni) on-rx))
	(recur ni (next stacks))))))

(defn- process-block-tree [stack on-block on-lx on-rx on-ty max-h gripper-pos #^HashSet block-set #^HashSet on-set #^HashMap num-map]
  (let [[block l-offset c-dist width height on-items] stack
	blx (+ l-offset on-lx)
	bcx (+ blx c-dist)
	brx (+ blx width)
	bty (+ on-ty height)]
    (util/assert-is (<= bty max-h))
    (util/assert-is (not (.contains block-set block)))
    (util/assert-is (< 0 c-dist width))
    (util/assert-is (not (and (< blx (first gripper-pos) brx)
			      (< on-ty (second gripper-pos) bty))))
    (.add block-set block)
    (.add on-set ['on block on-block])
    (.put num-map ['blockcx block] bcx)
    (.put num-map ['blockty block] bty)
    (.put num-map ['blocklw block] c-dist)
    (.put num-map ['blockrw block] (- width c-dist))
    (.put num-map ['blockh block] height)
    (process-block-forest on-items block blx brx bty max-h gripper-pos block-set on-set num-map)
    [blx brx]))
    ; return lx rx


(defn process-goal-stack [p t]
  (when (seq t)
    (let [[b f] t]
      (cons ['on b p]
	(apply concat (for [t f] (process-goal-stack b t)))))))

(defn process-goal-stacks [f]
  (apply concat 
	 (for [[b ons] f, on ons] 
	   (process-goal-stack b on))))
				  

(defn make-hybrid-blocks-strips-env 
  "Stacks is a forest of block info items (Table goes from -1 to 0 h, implicit).
   Each item is [block l-offset c-dist width height on-items].  Goal-stacks is same without numeric info."
  ([width height initial-pos stacks goal-stacks]
     (make-hybrid-blocks-strips-env width height initial-pos stacks goal-stacks nil))
  ([width height initial-pos stacks goal-stacks discrete-grid-size]
  (let [block-set (HashSet.)
	on-set    (HashSet.)
	num-map   (HashMap.)]
    (.add block-set 'table)
    (.put num-map ['blockcx 'table] 0)
    (.put num-map ['blockty 'table] 0)
    (.put num-map ['blocklw 'table] 0)
    (.put num-map ['blockrw 'table] width)
    (.put num-map ['blockh 'table] 1)    
    (process-block-forest stacks 'table 0 width 0 height initial-pos block-set on-set num-map)
    (hs/make-hybrid-strips-planning-instance 
     "hybrid-blocks"
     (make-hybrid-blocks-strips-domain)
     {'block (seq block-set)}
     (conj (set on-set) '[gripperempty])
     (assoc (into {} num-map)
       '[width] width
       '[height] height
       '[gripperx] (first initial-pos)
       '[grippery] (second initial-pos))
     (process-goal-stacks goal-stacks)
     str
     discrete-grid-size
     ))))


(comment 
  (make-hybrid-blocks-strips-env 2 2 [1 1] '[[a 0 0.1 0.2 0.1] [b 0.3 0.2 0.3 0.2]] '[[a [[b]]]])

  (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[a [[b]]]])

  (let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[a [[b]]]])]
    (get-hs-action env 'get {}))

(let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[a [[b]]]])]
	(visualize-hb-state 
	 (safe-apply-actions (get-initial-state env)
	  [(get-hs-action env 'get '{?b a ?c table})
	   (get-hs-action env 'up-holding '{?b a ?ngy 5.2})])))

(let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[a [[b]]]])
      as (get-action-space env)]
  (count (applicable-quasi-actions (get-initial-state env) as)))

  )

(util/deftest simple-hybrid-test
  (let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[b [[a]]]])]
    (util/is 
     (envs/satisfies-condition?  
       (envs/safe-apply-actions (envs/get-initial-state env)
	  [(hs/get-hs-action env 'get '{?b a ?c table})
	   (hs/get-hs-action env 'up-holding '{?b a ?ngy 4})
	   (hs/get-hs-action env 'right-holding '{?b a ?ngx 5})
	   (hs/get-hs-action env 'put '{?b a ?c b})])
       (envs/get-goal env)))))

(set! *warn-on-reflection* true)

(import '[javax.swing JFrame JPanel] '[java.awt Graphics])

(def #^JFrame *frame*  (JFrame.))
(def #^JPanel *panel*  (JPanel.))

(defn- get-blocks [numeric-vals]
  (set
    (for [[[f b] v] numeric-vals
	  :when (= f 'blockh)]
      b)))

(defn visualize-hb-state [[discrete-atoms numeric-vals]]
    (when (not (.isVisible *frame*))
      (def #^JPanel *panel* (JPanel.))
      (def #^JFrame *frame* (JFrame. "Hybrid Blocks State"))
      (doto *frame*
	(.add *panel*)
	(.setSize 400 400)
	(.setVisible true)))
    (let [#^Graphics g (.getGraphics *panel*)
	  height (util/safe-get numeric-vals '[height])
	  width  (util/safe-get numeric-vals '[width])
	  hpix (.getWidth *panel*)
	  vpix (dec (.getHeight *panel*))
	  xscale (/ hpix 1.0 width)
	  yscale (/ vpix 1.0 height)
	  scalex #(int (* xscale %))
	  posx   scalex
	  scaley #(int (* yscale %))
	  posy   #(- vpix (scaley %))
	  gx     (posx (util/safe-get numeric-vals '[gripperx]))
	  gy     (posy (util/safe-get numeric-vals '[grippery]))]
      (.removeAll *panel*)
      (.clearRect g 0 0 hpix (inc vpix))
      (doseq [b (disj (get-blocks numeric-vals) 'table)]
	(let [bcx (util/safe-get numeric-vals ['blockcx b])
	      blw (util/safe-get numeric-vals ['blocklw b])
	      brw (util/safe-get numeric-vals ['blockrw b])
	      bty (util/safe-get numeric-vals ['blockty b])
	      bh  (util/safe-get numeric-vals ['blockh  b])
	      #^String bs (str b)]
;	  (println bs (posy bty) (posy (- bty bh)))
	  (doto g
	    (.drawRoundRect (posx (- bcx blw)) (posy bty) (scalex (+ blw brw)) (scaley bh) 5 5)
	    (.drawOval (- (posx bcx) 3) (- (posy bty) 3) 6 6)
	    (.drawString bs (int (- (posx (+ bcx (/ (- brw blw) 2.0))) 3)) (int (+ (posy (- bty (/ bh 2.0))) 4))))
	  (when (contains? discrete-atoms ['holding b])
	    (.fillOval g (- (posx bcx) 3) (- (posy bty) 3) 6 6))
	  ))
      (doto g
	(.drawLine  gx 0 gx (+ gy 3))
	(.drawLine  (- gx 3) gy (+ gx 3) gy))
      ))
;      (.drawLine g 0 0 10 10))))
       
(set! *warn-on-reflection* false)

(defn animate-hb-seq [env action-names delay-ms]
  (reduce (fn [s a] 
	    (visualize-hb-state s)
	    (Thread/sleep delay-ms)
	    (envs/safe-next-state s (hs/get-hs-action env a)))
	  (envs/get-initial-state env) action-names))

(defn animate-random-hb-seq [env n-steps delay-ms]
  (let [as (envs/get-action-space env)]
    (loop [s (envs/get-initial-state env) n-steps n-steps]
   ;   (println s (map #(vector (:name (:schema %)) (:var-map %) (:num %)) (hs/applicable-quasi-actions s as)))
      (when (pos? n-steps)
	(visualize-hb-state s)
	(Thread/sleep delay-ms)
	(recur (envs/safe-next-state s (util/rand-elt (envs/applicable-actions s as)))
;		 (first (hs/all-quasi-action-instantiations 
;			 (util/rand-elt
;			  (hs/applicable-quasi-actions s as))
;			 as)))
	       (dec n-steps))))))
      

(comment 
  (visualize-hb-state (get-initial-state (make-hybrid-blocks-strips-env 2 2 [1 1] '[[a 0 0.1 0.2 0.1] [b 0.3 0.2 0.3 0.2]] '[[a [[b]]]])))


  (visualize-hb-state (get-initial-state ))

  (let [env (make-hybrid-blocks-strips-env 20 20 [14 10] '[[a 1 5 10 3 [[c 0 1 4 2] [d 4 2 6 5 [[e 1 1 2 9]]]]] [b 12 4 6 6 [[f 0 3 6 2 [[g 1 1 2 2] [h 4 1 2 2]]]]]] '[[a [[b]]]])]
	(visualize-hb-state 
	 (safe-apply-actions (get-initial-state env)
	  [(get-hs-action env 'get '{?b g ?c f})
	   (get-hs-action env 'up-holding '{?b g ?ngy 16})])))

  (let [env (make-hybrid-blocks-strips-env 20 20 [7 16] '[[a 1 5 10 3 [[c 0 1 4 2] [d 4 2 6 5 [[e 1 1 2 8]]]]] [b 12 4 6 6 [[f 0 3 6 2 [[g 1 1 2 2] [h 4 1 2 2]]]]]] '[[a [[b]]]])]
	(visualize-hb-state 
	 (safe-apply-actions (get-initial-state env)
	  [(get-hs-action env 'get '{?b e ?c d})
	   (get-hs-action env 'up-holding '{?b e ?ngy 18})
	   (get-hs-action env 'right-holding '{?b e ?ngx 11})])))

  (animate-hb-seq (make-hybrid-blocks-strips-env 20 20 [7 16] '[[a 1 5 10 3 [[c 0 1 4 2] [d 4 2 6 5 [[e 1 1 2 8]]]]] [b 12 4 6 6 [[f 0 3 6 2 [[g 1 1 2 2] [h 4 1 2 2]]]]]] '[[a [[b]]]])
		  '[[get e d] [up-holding e 18] [right-holding e 11]])

  (map :name (first (a-star-graph-search (ss-node (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]] 1)))))

  (map :name (first (a-star-graph-search (ss-node (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])))))

  (let [env (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]]) [as rew] (time (a-star-graph-search (ss-node env)))] (animate-hb-seq env (map :name as) 500) rew)

 ; Suboptimal due to split points, optimal with discrete grid = 1
 (let [env (make-hybrid-blocks-strips-env 10 4 [1 1] '[[a 1 3 6 1] [b 7 1 2 1 [[c 0 1 2 2]]]] '[[a [[b] [c]]]]) [as rew] (time (a-star-graph-search (ss-node env)))] (animate-hb-seq env (map :name as) 500) rew)
)


(comment 

(defn- get-and-check-sol [env]
  (map :name
    (first
     (envs/check-solution env
       (edu.berkeley.ai.search.algorithms.textbook/a-star-search 
	(edu.berkeley.ai.search/make-initial-state-space-node 
	 env   
	 (constantly 0)))))))

(util/deftest flat-nav-switch
  (util/testing "non-strips"
    (util/is (= ['left 'flip 'down]
     (get-and-check-sol 
      (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1])))))
  (util/testing "strips"
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/constant-predicate-simplify
       (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])))))
    (util/is (= '[[good-left x1 x0] [flip-v x0 y0] [good-down y0 y1]]
     (get-and-check-sol
      (strips/flatten-strips-instance
       (strips/constant-predicate-simplify
	(make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1]))))))))


)
  
  
(comment 
  (u util search search.algorithms.textbook domains.nav-switch)
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0) 100 1))
  (map :name (first (a-star-search (state-space-search-node (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) (constantly 0)))))
  (binding [*debug-level* 1] (lrta-star (make-nav-switch-env 2 2 [[0 0]] [1 0] true [0 1]) #(reduce + (map (comp (fn [x] (* -2 (Math/abs x))) -) (:pos %) [0 1])) 10 1))

  (dotimes [_ 3] (time (map :name (first (a-star-search (state-space-search-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))))
  ; right now STRIPS is about equal in speed to hand-coded, with new successor generator!
    ; TODO: reachability analysis (planning graph?)

  (time (second (a-star-search (make-initial-state-space-node (make-nav-switch-strips-env 6 6 [[1 1]] [5 0] true [0 5]) (constantly 0)))))
 ; "Elapsed time: 3596.095 msecs"

  (time (second (a-star-search (make-initial-state-space-node (constant-predicate-simplify (make-nav-switch-strips-env 2 2 [[0 0]] [1 0] true [0 1])) (constantly 0)))))

  )
