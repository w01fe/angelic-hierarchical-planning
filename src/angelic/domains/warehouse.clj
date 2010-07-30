(ns w01fe.domains.warehouse
 (:import [java.util HashSet HashMap])
 (:require [edu.berkeley.ai [util :as util]] 
           [w01fe [env :as env] [hierarchy :as hierarchy]]))

; Note: WW heuristic is inconsistent.



(defn- make-dir [s name [dx dy]]
  (let [[cx cy :as cp] (env/get-var s '[at])
        [w h]          (get (env/get-var s :const) '[topright])
        nx (+ cx dx), ny (+ cy dy)]
    (when (and (<= 1 nx w) (<= 1 ny h) (not (env/get-var s ['someblockat nx ny])))
      (env/FactoredPrimitive
       name
       {['at] cp ['someblockat nx ny] false}
       {['at] [nx ny]}
       -1))))

(defn- make-left  [s] (make-dir s '[left]  [-1 0 ]))
(defn- make-right [s] (make-dir s '[right] [ 1 0 ]))
(defn- make-down  [s] (make-dir s '[down]  [ 0 -1]))
(defn- make-up    [s] (make-dir s '[up]    [ 0  1]))


(defn- make-specific-turn [pos cur-fr]
  (env/FactoredPrimitive [(if cur-fr 'turn-l 'turn-r)] {['at] pos ['facingright] cur-fr} 
                         {'[facingright] (not cur-fr)} -1))

(defn- make-turn   [s]
  (let [[cx cy] (env/get-var s '[at])
        cur-fr  (env/get-var s '[facingright])]
    (when (= cy (nth (get (env/get-var s :const) '[topright]) 1))  
      (make-specific-turn [cx cy] cur-fr))))


(defn- make-specific-get [b c fr? gx gy]
  (let [bx (+ gx (if fr? 1 -1))]
    (env/FactoredPrimitive
     [(if fr? 'get-r 'get-l) b c]
     {'[at] [gx gy] '[facingright] fr? ['blockat bx gy] b 
      ['on c] b ['on b] nil '[holding] nil}
     {['blockat bx gy] nil ['on c] nil ['someblockat bx gy] false ['holding] b}
     -1)))

(defn- make-get [s]
  (when-not (env/get-var s ['holding])
    (let [[cx cy] (env/get-var s '[at])
          cur-fr  (env/get-var s '[facingright])
          [width] (get (env/get-var s :const) '[topright])
          bx      (+ cx (if cur-fr 1 -1))]
      (when-let [b (and (<= 1 bx width) (env/get-var s ['blockat bx cy]))]
        (when-not (env/get-var s ['on b])
          (let [c (env/get-var s ['blockat bx (dec cy)])]
            (make-specific-get b c cur-fr cx cy)))))))

(defn- make-specific-put [b c fr? gx gy]
  (let [bx (+ gx (if fr? 1 -1))]
    (env/FactoredPrimitive
     [(if fr? 'put-r 'put-l) b c]
     {'[at] [gx gy] '[facingright] fr? ['blockat bx (dec gy)] c 
      ['on c] nil '[holding] b}
     {['blockat bx gy] b ['on c] b ['someblockat bx gy] true ['holding] nil}
     -1)))

(defn- make-put [s]
  (when-let [b (env/get-var s ['holding])]
    (let [[cx cy] (env/get-var s '[at])
          cur-fr  (env/get-var s '[facingright])
          [width] (get (env/get-var s :const) '[topright])
          bx      (+ cx (if cur-fr 1 -1))]
      (when-let [c (and (<= 1 bx width) (env/get-var s ['blockat bx (dec cy)]))]
        (when-not (env/get-var s ['on c])
          (make-specific-put b c cur-fr cx cy))))))



(deftype WarehouseEnv [init goal topright] :as this
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

; state vars are: (const), at, facingright, holding, blockat, someblockat, on
; initial-stacks is map from column number to stacks of block names (top-down).
; goal-stacks is seq of desired stacks
(defn make-warehouse-env 
  [width height initial-pos initial-faceright? initial-stacks initial-holding goal-stacks]
  (let [bottomleft [1 1]
        topright   [width height]
        blocks     (set (util/cons-when initial-holding (apply concat (vals initial-stacks))))
        tables     (set (for [i (range 1 (inc width))] (util/symbol-cat 'table i)))]
    (assert (not (contains? blocks nil)))
    (assert (empty? (clojure.set/intersection tables blocks)))
    (assert (every? identity (map <= [1 1] initial-pos topright)))
    (assert (every? #(<= 1 % width) (keys initial-stacks)))
    (assert (every? #(< (count %) height) (vals initial-stacks)))
    (assert (every? (into blocks tables) (apply concat goal-stacks)))
    (assert (< (count (get initial-stacks (first initial-pos))) (second initial-pos)))
    (let [stacks (vec (for [i (range 1 (inc width))] 
                        (vec (take height (concat [(util/symbol-cat 'table i)] 
                                                  (reverse (get initial-stacks i)) 
                                                  (repeat nil))))))]
      (WarehouseEnv 
       (into {:const {['topright] topright}
              '[at]  (vec initial-pos)
              '[facingright] (if initial-faceright? true false)
              '[holding]     (or initial-holding nil)}
             (apply concat    
                    (for [[x stack] (util/indexed stacks)
                          [y block] (util/indexed stack)
                          :let [x (inc x) y (inc y)]]
                      (util/cons-when
                       (when block [['on block] (or (get stack y) nil)])
                       [[['blockat x y] (or block nil)]
                        [['someblockat x y] (if block true false)]]))))
       (into {} (for [stack goal-stacks, [a b] (partition 2 1 stack)] [['on b] a]))
       topright))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Simple Nav ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype SimpleNavHLA [name context dest] :as this
  env/Action                (action-name [] name)
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] context )
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (if (= dest (env/get-var s ['at]))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)]
                                     :when a]
                                 [a this])))
                            (cycle-level- [s] 1))


;Issue with context: we also learn for other initial states, possibly outside initial range.
(defn make-simple-nav-hla [dx dy nav-context]
  (SimpleNavHLA ['nav dx dy] nav-context [dx dy]))
   ;(into '#{[at]} (for [x (incl-range dx gx) y (range (min dy gy) (inc h))] ['someblockat x y])) [dx dy]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  URD   Nav ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype UpHLA [opt-dy] :as this
  env/Action                (action-name [] ['up-to opt-dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] '#{[at]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [[cx cy] (env/get-var s '[at])]
                                (filter identity
                                  [(when (or (not opt-dy) (= cy opt-dy)) [])
                                   (when (or (not opt-dy) (< cy opt-dy))
                                     (when-let [a (make-up s)] [a this]))])))
                            (cycle-level- [s] nil))

(deftype DownHLA [dx dy] :as this
  env/Action                (action-name [] ['down-to dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] #{'[at] ['someblockat dx dy]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [[cx cy] (env/get-var s '[at])]
                                (assert (= cx dx))
                                (filter identity
                                  [(cond (= cy dy) []
                                         (> cy dy) (when-let [a (make-down s)] [a this]))])))
                            (cycle-level- [s] nil))

(defn incl-range 
  ([x1 x2] (if (<= x1 x2) (range x1 (inc x2)) (range x2 (inc x1))))
  ([x1 x2 x3] (range (min x1 x2 x3) (inc (max x1 x2 x3)))))

(deftype TraverseHLA [dx] :as this
  env/Action                (action-name [] ['traverse-to dx])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (let [[cx cy] (env/get-var s '[at])]
                                (into '#{[at]} (for [x (incl-range cx dx)] ['someblockat x cy]))))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [[cx cy] (env/get-var s '[at])]
                                (filter identity
                                  [(cond (= cx dx) []
                                         (> cx dx) (when-let [a (make-left s)] [a this])
                                         (< cx dx) (when-let [a (make-right s)] [a this]))])))
                            (cycle-level- [s] nil))

(defn make-fancy-nav-plan [dx dy h]
  (if (= dy h)
      [(UpHLA dy) (TraverseHLA dx)]
    [(UpHLA nil) (TraverseHLA dx) (DownHLA dx dy)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Hierarchy ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


 

; state vars are: (const), at, facingright, holding, blockat, someblockat, on

(deftype MoveBlockHLA [env name context nav-factory b bx by a c cx cy] :as this
    env/Action                (action-name [] name)
                              (primitive? [] false)
    env/ContextualAction      (precondition-context [s] context)
    hierarchy/HighLevelAction 
      (immediate-refinements- [s]
        (assert (= b (env/get-var s ['blockat bx by])))
        (assert (= a (env/get-var s ['blockat bx (dec by)])))                                             (assert (= c (env/get-var s ['blockat cx cy])))                                           
        (let [[w h] (get (env/get-var s :const) '[topright])
  ;                                      [gx gy]  (env/get-var s '[at])
              fr?   (env/get-var s '[facingright])
              dirs  '[[true 1] [false -1]]]
          (for [[fr1 dx1] dirs
                :let [gx1  (- bx dx1), gy1 by]
                :when (and (<= 1 gx1 w) (not (env/get-var s  ['someblockat gx1 gy1])))
                [fr2 dx2] dirs
                :let [gx2  (- cx dx2), gy2 (inc cy)]
                :when (and (<= 1 gx2 w) 
                           (contains? #{nil b} (env/get-var s ['blockat gx2 gy2])))]
            (concat
             (when (not (util/truth= fr? fr1))
               (conj (nav-factory gx1 h) (make-specific-turn [gx1 h] fr?)))
             (nav-factory gx1 gy1)
             [(make-specific-get b a fr1 gx1 gy1)]
             (when (not (util/truth= fr1 fr2))
               (conj (nav-factory gx2 h) (make-specific-turn [gx2 h] fr1)))
             (nav-factory gx2 gy2)
             [(make-specific-put b c fr2 gx2 gy2)]))))
      (cycle-level- [s] nil))

(defn make-move-block-hla [env nav-context nav-factory b bx by a c cx cy]
  (MoveBlockHLA env ['move-block b c]
                (into nav-context
                      ['[facingright] ['on a] ['on c] '[holding]
                       ['blockat bx by] ['blockat cx (inc cy)]]) 
                nav-factory b bx by a c cx cy))


(declare possible-move-refinements)

(deftype MoveBlocksHLA [env goal-fn context nav-context nav-factory block-off-limits] :as this
    env/Action                (action-name [] ['move-blocks block-off-limits ])
                              (primitive? [] false)
    env/ContextualAction      (precondition-context [s] context)
    hierarchy/HighLevelAction (immediate-refinements- [s] 
                                 (possible-move-refinements env goal-fn context nav-context 
                                                            nav-factory block-off-limits s))
                              (cycle-level- [s] 2))

; Note: differs from previous (strips) version in use of goal test.
;; TODO: should allow self-moves? 
(defn possible-move-refinements [env goal-fn context nav-context nav-factory block-off-limits state]
  (let [[w h] (get (env/get-var state :const) '[topright])
        tops  (for [x (range 1 (inc w))] 
                [x (last (take-while #(and (<= % h) (env/get-var state ['someblockat x %])) (range 1 (inc h))))])]
    (util/cons-when
     (when (goal-fn state) [])
     (for [[bx by] tops
           :let [b (env/get-var state ['blockat bx by])]
           :when (and (> by 1) (not (= b block-off-limits))) 
           [cx cy] tops
           :let [c (env/get-var state ['blockat cx cy])]
           :when (and (< cy h) (not (= b c)))]
       [(make-move-block-hla env nav-context nav-factory
                             b bx by (env/get-var state ['blockat bx (dec by)]) c cx cy)
        (MoveBlocksHLA env goal-fn context nav-context nav-factory b)]))))

(defn make-nav-context [env]
  (let [ [w h] (:topright env)]
    (set (cons '[at] (for [x (range 1 (inc w)) y (range 2 (inc h))] ['someblockat x y])))))

(deftype WarehouseTLA [env context nav-context nav-factory] :as this
    env/Action                (action-name [] '[top])
                              (primitive? [] false)
    env/ContextualAction      (precondition-context [s] context)
    hierarchy/HighLevelAction (immediate-refinements- [s] 
                                 (let [goal-fn (env/goal-fn env)]
                                   (possible-move-refinements 
                                    env goal-fn context nav-context nav-factory nil s)))
                              (cycle-level- [s] nil))
 

(defn make-warehouse-tla [env]
  (let [nav-context (make-nav-context env)]
    (WarehouseTLA env (util/keyset (dissoc (env/initial-state env) :const))
                  nav-context (fn [dx dy] [(make-simple-nav-hla dx dy nav-context)]))))

(defn simple-warehouse-hierarchy [#^WarehouseEnv env]
  (hierarchy/SimpleHierarchicalEnv env [(make-warehouse-tla env)]))


(defn make-warehouse-tla-fancynav [env]
  (let [nav-context (make-nav-context env)
        [w h]       (:topright env)]
    (WarehouseTLA env (util/keyset (dissoc (env/initial-state env) :const))
                  nav-context (fn [dx dy] (make-fancy-nav-plan dx dy h)))))

(defn simple-warehouse-hierarchy-fancynav [#^WarehouseEnv env]
  (hierarchy/SimpleHierarchicalEnv env [(make-warehouse-tla-fancynav env)]))

;; TODO: heuristic
;; TODO: missing precond handling && preconds ? 

(comment 


  (defn warehouse-hungarian-heuristic [env s] "destination-to-destination."
    (let [[cx cy] (map #(env/get-var s [%]) '[atx aty])
          pass    (remove #(env/get-var s ['pass-served? (first %)]) (:passengers env))]
      (if (empty? pass) 0
          (int (Math/floor 
                (util/maximum-matching
                 (cons ::current (map first pass))
                 (cons ::goal    (map first pass))
                 (concat
                  (for [[p1 _ [dx1 dy1]]         (cons [::current nil [cx cy]] pass)
                        [p2 [sx2 sy2] [dx2 dy2]] pass]
                    [p1 p2
                     (- -2
                        (util/abs (- dx1 sx2)) (util/abs (- dy1 sy2))
                        (util/abs (- dx2 sx2)) (util/abs (- dy2 sy2)))])        
                  (for [[p [sx sy] [dx dy]] pass]
                    [p ::goal 0]))))))))

)







(comment 
  (time (debug 0 (uniform-cost-search (make-warehouse-env 2 2 [2 2] false {1 '[a]} nil ['[a table2]]))))
  (time (debug 0 (uniform-cost-search (make-warehouse-env 3 3 [2 2] false {1 '[a] 3 '[b]} nil ['[a b]]))))
  (time (debug 0 (uniform-cost-search (make-warehouse-env 4 4 [2 3] false {1 '[a] 3 '[c b]} nil ['[a c table1]]))))

  ;; TODO: hierarchy somehow beats non for this ?! 
(let [e (make-warehouse-env 2 2 [2 2] false {1 '[a]} nil ['[a table2]]) h (w01fe.warehouse/simple-warehouse-hierarchy e)]  
  (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
  (doseq [alg `[sahtn-dijkstra  sahucs-simple sahucs-dijkstra sahucs-inverted]]
         (time (debug 0 (println alg (run-counted #(second ((resolve alg) h))))))))

(let [e (make-warehouse-env 4 4 [2 3] false {1 '[a] 3 '[c b]} nil ['[a c table2]]) h (w01fe.warehouse/simple-warehouse-hierarchy e)]  
  (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
  (doseq [alg `[sahtn-dijkstra  sahucs-simple sahucs-dijkstra sahucs-inverted]]
         (time (debug 0 (println alg (run-counted #(second (w01fe.env/verify-solution e ((resolve alg) h)))))))))

(let [e (make-warehouse-env 6 5 [1 5] false {1 '[a c] 4 '[e g]} nil '[[a e table2] [c g table5]]) h (w01fe.warehouse/simple-warehouse-hierarchy e)]  
  (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
  (doseq [alg `[sahtn-dijkstra  sahucs-simple sahucs-dijkstra sahucs-inverted]]
         (time (debug 0 (println alg (run-counted #(second (w01fe.env/verify-solution e ((resolve alg) h)))))))))
  )


