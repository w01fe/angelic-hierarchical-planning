(ns edu.berkeley.ai.domains.hybrid-blocks
 (:import [java.util HashMap HashSet])
 (:use clojure.test )
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.hybrid-strips :as hs]
           [edu.berkeley.ai.angelic :as angelic]
	   [edu.berkeley.ai.angelic.hybrid
            [continuous-lp-states :as cls]
            [fixed-lp-valuations :as hflv]
            [dnf-lp-valuations :as hdlv]]
    )
 )

;; Idea for heuristic: have "goal-cx", "goal-ty" variables for each block appearing in goal
;; Constrain these to match goal configuration as much as possible.
;; Penalize absolute-value distances from current positions (requires second set of vars).  

;; Can't easily do this, even in NCStrips, since we must introduce a parameterized set of variables.

;; Would be easier if we had state abstraction hierarchy, since we wouldn't have to explicitly
;; constrain goal positions (would be handled by "finish").

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           Domain helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
		

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                              Public Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;		  

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
    (doseq [b block-set]    (.put num-map ['nblockson b] 0))
    (doseq [[_ a b] on-set] (.put num-map ['nblockson b] (inc (.get num-map ['nblockson b]))))
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


(def *hybrid-blocks-hierarchy* (util/path-local "hybrid_blocks.hierarchy"))
(def *hybrid-blocks-hierarchy-unguided* (util/path-local "hybrid_blocks_unguided.hierarchy"))






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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                               Heuristic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Defines a simple heuristic that only takes the total distance blocks
; need to move into account, as well as an approximation of get and put costs.

(def *hb-holding-movement-reward* -2)
(def *hb-get-reward*              -1)
(def *hb-put-reward*              -1)

(derive ::HybridBlocksActDescriptionSchema ::angelic/Description)

(defmethod angelic/parse-description :hybrid-blocks-act [desc domain params]
  {:class ::HybridBlocksActDescriptionSchema})


(derive ::HybridBlocksActDescription ::angelic/Description)

(defmethod angelic/instantiate-description-schema ::HybridBlocksActDescriptionSchema [desc instance]
  (let [goal-atoms (util/safe-get instance :goal-atoms)]
    (assoc desc 
      :class 
        ::HybridBlocksActDescription
      :goal 
        (envs/get-goal instance)
      :goal-ons 
        (set (for [a goal-atoms] 
               (do (assert (= (first a) 'on))
                   a)))
      :goal-blocks 
         (into {} 
           (for [b (set (apply concat (map rest goal-atoms)))]
             [b [(util/symbol-cat b "fx") (util/symbol-cat b "fy")]])))))
	  

(defmethod angelic/ground-description ::HybridBlocksActDescription [desc var-map] desc)
  

(defn hb-discrete-reward
  "Take a set of goal 'on' atoms, a set of state 'on' atoms, and possibly
   a true 'holding' atom, and return a reward for get and put actions."
  [goal-ons state-ons state-holding]
  (when state-holding (assert (= (first state-holding) 'holding)))
  (+ 
    (* (count (util/difference-coll goal-ons state-ons))
       (+ *hb-get-reward* *hb-put-reward*))
    (cond (not state-holding)
             0 
          (some #(= (second state-holding) (second %)) goal-ons) 
             (- *hb-get-reward*)
          :else 
             *hb-put-reward*)))

(defn hb-clause-discrete-reward
  [desc possible-atoms]
  (hb-discrete-reward
   (util/safe-get desc :goal-ons)
   (filter #(= (first %) 'on)  possible-atoms)
   (first (filter #(= (first %) 'holding) possible-atoms))))

(defn transform-hb-clp 
  "Add heuristic terms to the CLP, corresponding to all of the necessary
   on relations holding.  Basic idea: add new variables for x and y positions
   of all blocks mentioned, constrain them to match the on relation, and then
   charge for sum of absolute values of distances from current locations.
   goal-blocks maps block names to usable [final-x final-y] variable names."
  [clp goal-blocks goal-ons extra-reward]
  (cls/update-lp-state 
   (reduce 
    (fn [clp [_ b c]]
      (let [[bx by] (util/safe-get goal-blocks b)
            [cx cy] (util/safe-get goal-blocks c)]
        (cls/constrain-lp-state-lez
         (cls/constrain-lp-state-gez 
          (cls/constrain-lp-state-eqz clp 
           {by 1, ['blockh b] -1, cy -1})
          {bx 1, ['blocklw b] -1, cx -1, ['blocklw c] 1} false)
         {bx 1, ['blockrw b] +1, cx -1, ['blockrw c] -1} false)))
    (reduce (fn [clp [b [bx by]]]
              (cls/add-lp-state-param 
               (cls/add-lp-state-param clp bx)
               by [{['blockh b] 1} {['height] 1}] nil)) 
            clp goal-blocks)
    goal-ons)
   nil
   (into {} 
      (cons [nil extra-reward]
        (apply concat
         (for [[b [bx by]] goal-blocks]
           [[{bx 1 ['blockcx b] -1}           
             *hb-holding-movement-reward*]
            [{by 1 ['blockty b] -1}           
             *hb-holding-movement-reward*]]))))))

(defmethod angelic/progress-valuation [::angelic/PessimalValuation ::HybridBlocksActDescription] 
  [val desc]  val)

(defmethod angelic/progress-valuation [::hflv/HybridFixedLPValuation ::HybridBlocksActDescription] [val desc]
  (let [discrete-reward (hb-clause-discrete-reward desc (util/safe-get val :discrete-state))
        goal-blocks (util/safe-get desc :goal-blocks)
        goal-ons (util/safe-get desc :goal-ons)]
    (angelic/make-conditional-valuation 
    ; (:goal desc)
     envs/*true-condition*
     (apply max
       Double/NEGATIVE_INFINITY
       (for [c (util/safe-get val :continuous-lp-states)
             :let [rew (last (cls/solve-lp-state (transform-hb-clp c goal-blocks goal-ons discrete-reward)))]
             :when rew]
         rew)))))

(defmethod angelic/progress-valuation [::hdlv/HybridDNFLPValuation ::HybridBlocksActDescription] [val desc]
  (let [goal-blocks (util/safe-get desc :goal-blocks)
        goal-ons (util/safe-get desc :goal-ons)]
    (angelic/make-conditional-valuation 
     ;(:goal desc)
          envs/*true-condition*
     (apply max
       Double/NEGATIVE_INFINITY
       (for [[d c] (util/safe-get val :clause-lp-set)
             :let [rew (last (cls/solve-lp-state 
                              (transform-hb-clp c goal-blocks goal-ons 
                                                (hb-clause-discrete-reward desc (keys d)))))]
             :when rew]
         rew)))))

(defn make-hybrid-blocks-heuristic [env]
  (let [d (angelic/ground-description (angelic/instantiate-description-schema (angelic/parse-description [:hybrid-blocks-act] nil nil) env) {})]
    #(angelic/valuation-max-reward (angelic/progress-valuation % d))
    ))

(defn make-flat-hybrid-blocks-heuristic [env]
  (let [d (angelic/ground-description (angelic/instantiate-description-schema (angelic/parse-description [:hybrid-blocks-act] nil nil) env) {})]
    (fn [s] (angelic/valuation-max-reward (angelic/progress-valuation (angelic/state->valuation   ::hflv/HybridFixedLPValuation s) d)))))


(deftest hybrid-blocks-heuristic ;; TODO: extend.
  (is (= -10
         (let [e (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])]
           ((make-flat-hybrid-blocks-heuristic e) (envs/get-initial-state e))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                              Visualization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(set! *warn-on-reflection* true)

(import '[javax.swing JFrame JPanel] '[java.awt Graphics])

(def #^JFrame *frame*  (JFrame.))
(def #^JPanel *panel*  (JPanel.))

(defn- get-blocks [numeric-vals]
  (set
    (for [[[f b] v] numeric-vals
	  :when (= f 'blockh)]
      b)))

(defn visualize-hb-state [state]
    (when (not (.isVisible *frame*))
      (def #^JPanel *panel* (JPanel.))
      (def #^JFrame *frame* (JFrame. "Hybrid Blocks State"))
      (doto *frame*
	(.add *panel*)
	(.setSize 400 400)
	(.setVisible true)))
    (let [[discrete-atoms numeric-vals] state
	  #^Graphics g (.getGraphics *panel*)
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
      )
    state)
;      (.drawLine g 0 0 10 10))))
       
(set! *warn-on-reflection* false)


(defn animate-hb-seq [env action-names delay-ms]
  (visualize-hb-state 
  (reduce (fn [s a] 
	    (visualize-hb-state s)
	    (Thread/sleep delay-ms)
	    (envs/safe-next-state s (hs/get-hs-action env a)))
	  (envs/get-initial-state env) action-names)))

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

 ; Similar, but requires extra move
 ; can be used with discrete grid 2
 (let [env (make-hybrid-blocks-strips-env 11 8 [9 8] '[[d 1 1 2 2 [[e 0 1 2 2]]] [a 3 3 6 2] [b 9 1 2 4 [[c 0 1 2 4]]]] '[[a [[b] [c [[e]]] [d]]]]) [as rew] (time (a-star-graph-search (ss-node env)))] (animate-hb-seq env (map :name as) 500) rew)


(def *env* (make-hybrid-blocks-strips-env 22 20 [10 15] '[[a 1 4 10 5 [[b 1 3 5 2] [c 6 1 2 8]]] [d 11 2 3 7] [e 15 4 7 8 [[f 0 3 7 4]]]] '[[a [[f]]]]))
(def *sol* (map :name (first (a-star-graph-search (ss-node *env*))))) 


;; Simple, solvable problem
(time  (let [e (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])]
               (map :name (extract-hybrid-primitive-solution e (first (a-star-search (alt-node (get-hierarchy *hybrid-blocks-hierarchy* e) {:cache? false :graph? false :ref-choice-fn first-choice-fn})))))))


;; Takes way too long in current setup.
(time  (let [e (make-hybrid-blocks-strips-env 15 6 [1 1] '[[a 1 2 5 1] [b 7 1 2 1] [c 10 1 2 2]] '[[a [[b] [c]]]])]
               (map :name (extract-hybrid-primitive-solution e (first (a-star-search (alt-node (get-hierarchy *hybrid-blocks-hierarchy* e) {:cache? false :graph? false :ref-choice-fn first-choice-fn})))))))
)




(comment 
(time  (let [e (make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 0 2 3 1] [b 4 1 2 1]] '[[a [[b]]]])]
               (map :name (extract-hybrid-primitive-solution e (time  (first (a-star-search (alt-node (get-hierarchy *hybrid-blocks-hierarchy* e) {:cache? false :graph? false :ref-choice-fn first-choice-fn}))))))))
)