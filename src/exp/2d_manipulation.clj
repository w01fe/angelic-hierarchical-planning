(ns exp.2d-manipulation
;  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [sas :as sas] [hierarchy :as hierarchy]])
  (:import [java.util Random]))

; This is meant to be a simplified version of the ICAPS '10/SAHTN 
; mobile manipulation domain.  In particular, we abstract away most of
; the robot, while trying to maintain the same domain structures.

; This could be done as discrete or continuous.  Doesn't really matter here,
; but we need to decide how we're handling angelic sets, etc. 
; May as well be discrete, so we can use SAS machinery.

; Seems we need all the angelic machinery we had before, in general case.

;; State variables are:
; :const {[height] [width] [freespace] [goal o] ...}
;    freespace is set of free [x y] pairs.
;    goal is [[minx miny] [maxx maxy]] range -- inclusive.
; [cx], [cy] - current "base" coordinates.
; [gxo], [gyo] - gripper x and y offsets.  
; [x o], [y o] - location of object
; [at-goal? o]


(defn- make-left   [s]
  (let [cx (env/get-var s '[atx])]
    (when (> cx 1) 
      (env/FactoredPrimitive ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn- make-right  [s]
  (let [const (env/get-var s :const)
        width  (get const '[width])
        cx     (env/get-var s '[atx])]
    (when (< cx width)  
      (env/FactoredPrimitive ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn- make-down  [s]
  (let [cy     (env/get-var s '[aty])]
    (when (> cy 1)
      (env/FactoredPrimitive ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn- make-up    [s]
  (let [const (env/get-var s :const)
        height (get const '[height])
        cy     (env/get-var s '[aty])]
    (when (< cy height)
      (env/FactoredPrimitive ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn- make-pickup  [s pass [x y]]
  (env/FactoredPrimitive 
   ['pickup pass x y] 
   {['atx]        x     ['aty]        y
    ['passx pass] x     ['passy pass] y}
   {['passx pass] :2d-manipulation ['passy pass] :2d-manipulation}
   -1))

(defn- make-dropoff [s pass [x y]]
  (when pass 
    (env/FactoredPrimitive 
     ['dropoff pass x y] 
     {['atx]        x     '[aty] y 
      ['passx pass] :2d-manipulation ['passy pass] :2d-manipulation}
     {['passx pass] x     ['passy pass] y}
     -1)))


(deftype Infinite2d-ManipulationEnv [width height passengers] :as this
 env/Env
  (initial-state []
    (into {:const {['width] width ['height] height}
           ['atx] 1 ['aty] 1}
          (apply concat
            (for [[name [sx sy]] passengers]
              [[['passx name] sx] [['passy name] sy]]))))
  (actions-fn []
   (fn 2d-manipulation-actions [s]
     (filter identity
       (apply concat 
         (map #(% s) [make-left make-right make-up make-down])
         (for [[pass] passengers x (range 1 (inc width)) y (range 1 (inc height))] 
           [(make-pickup s pass [x y]) (make-dropoff s pass [x y])])))))
  (goal-fn [] 
    (let [goal-map (env/goal-map this)]
      #(when (env/state-matches-map? % goal-map)
         (env/solution-and-reward %))))
 env/FactoredEnv
  (goal-map [] 
    (into {} 
      (apply concat
        [[['atx] width] [['aty] height]]
        (for [[pass _ [dx dy]] passengers] 
          [[['passx pass] dx] [['passy pass] dy]])))))


(defn make-random-infinite-2d-manipulation-env 
  ([width height n-passengers] 
     (make-random-infinite-2d-manipulation-env width height n-passengers (rand-int 10000000)))
  ([width height n-passengers seed]
     (let [r (Random. seed)]
       (.nextDouble r) (.nextDouble r)
       (Infinite2d-ManipulationEnv width height
                (for [i (range n-passengers)]
                  [(symbol (str "pass" i))
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]])))))

(require 'exp.ucs)
(deftest infinite-2d-manipulation
  (is (= -15 (second (exp.ucs/uniform-cost-search (Infinite2d-ManipulationEnv 5 5 [[:red [2 1] [5 4]] [:green [1 4] [3 3]]]))))))



;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy ;;;;;;;;;;;;;;;;;;;;;
; Mostly copied from 2d-manipulation. 

(deftype NavHLA [env dx dy] :as this
  env/Action                (action-name [] ['nav dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] #{['atx] ['aty]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (if (and (= dx (env/get-var s ['atx])) 
                                      (= dy (env/get-var s ['aty])))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)]
                                     :when a]
                                 [a this])))
                            (cycle-level- [s] 1)
  env/AngelicAction         (optimistic-map [s]
                              (let [cx (env/get-var s ['atx])
                                    cy (env/get-var s ['aty])]
                                {(env/set-var (env/set-var s ['atx] dx) ['aty] dy)
                                 (- 0 (util/abs (- dx cx)) (util/abs (- dy cy)))}))
                            (pessimistic-map [s] 
                              (env/optimistic-map this s)))

(deftype Infinite2d-ManipulationTLA [env context]      :as this
  env/Action                (action-name [] ['top])
                            (primitive? [] false)  
  env/ContextualAction      (precondition-context [s] context)
  hierarchy/HighLevelAction 
  (immediate-refinements- [s]
    (let [held-p (set (filter #(= :2d-manipulation (env/get-var s ['passx (first %)])) (:passengers env)))
          src-p  (remove #(or (held-p %) (env/get-var s ['pass-served? (first %)])) (:passengers env))
          all-nxt (concat (for [[n _ [dx dy]] held-p] [(NavHLA env dx dy) (make-dropoff :dummy n [dx dy])])
                          (for [[n [sx sy] _]  src-p] [(NavHLA env sx sy) (make-pickup  :dummy n [sx sy])]))]
      (if (empty? all-nxt)
        (let [{:keys [width height]} env]
          [[(NavHLA env width height) (env/make-finish-action env)]])
        (map #(conj (vec %1) this) all-nxt))))
   (cycle-level- [s] nil)
  env/AngelicAction         (optimistic-map [s]
                              {(env/set-vars s (env/make-finish-goal-state env))})
                            (pessimistic-map [s] {}))

(defn make-infinite-2d-manipulation-tla [env]
  (Infinite2d-ManipulationTLA env (util/keyset (dissoc (env/initial-state env) :const))))

(defn simple-2d-manipulation-hierarchy [#^Inf2d-ManipulationEnv env]
  (hierarchy/SimpleHierarchicalEnv
   env
   [(make-infinite-2d-manipulation-tla env)]))

