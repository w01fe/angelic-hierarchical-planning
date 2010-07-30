(ns angelic.domains.nav-switch
  (:require [edu.berkeley.ai.util :as util]
            [angelic [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util Random]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-dir [s name h? dir]
  (let [dim   (if h? '[x] '[y])
        cur-h (env/get-var s '[h])
        ov    (env/get-var s dim)
        nv    (+ ov dir)]
    (when (<= 1 nv (get (env/get-var s :const) dim))
      (env/FactoredPrimitive name {dim ov, '[h] cur-h} {dim nv} 
                             (if (util/truth= cur-h h?) -2 -4)))))

(defn- make-left  [s] (make-dir s '[left]  true  -1))
(defn- make-right [s] (make-dir s '[right] true   1))
(defn- make-up    [s] (make-dir s '[up]    false  1))
(defn- make-down  [s] (make-dir s '[down]  false -1))


(defn make-specific-switch [cur-h cur-x cur-y]
  (env/FactoredPrimitive 
   [(if cur-h 'v 'h)] {'[h] cur-h '[x] cur-x '[y] cur-y} {'[h] (not cur-h)} -1))


(defn make-switch [s]
  (let [cur-h (env/get-var s '[h])
        cur-x (env/get-var s '[x])
        cur-y (env/get-var s '[y])]
    (when (contains? (get (env/get-var s :const) :switch-set) [cur-x cur-y])
      (make-specific-switch cur-h cur-x cur-y))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Env ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype NavSwitchEnv [width height sx sy sh? gx gy switch-set] :as this
  env/Env
  (initial-state [] 
    {'[x] sx '[y] sy '[h] (if sh? true false)
     :const {'[x] width '[y] height :switch-set switch-set}})
  (actions-fn []
   (fn nav-switch-actions [s]
     (filter identity (map #(% s) [make-left make-right make-up make-down make-switch]))))
  (goal-fn [] 
    (let [goal-map (env/goal-map this)]
      #(when (env/state-matches-map? % goal-map)
         (env/solution-and-reward %))))
 env/FactoredEnv
  (goal-map [] {'[x] gx '[y] gy}))

(defn make-random-switch-set [width height n seed]
  (let [r (Random. (long seed))
        width (int width) height (int height)]
    (.nextDouble r) (.nextDouble r)    
    (set (take n (distinct (repeatedly #(vector (inc (.nextInt r width)) 
                                                (inc (.nextInt r height)))))))))

(defn make-nav-switch-env [size [sx sy] init-h [gx gy] switch-set]
  (NavSwitchEnv size size sx sy init-h gx gy switch-set))

(defn make-random-nav-switch-env 
  ([size n-switches] 
     (make-random-nav-switch-env size n-switches (rand-int 10000000)))
  ([size n-switches seed]
     (make-nav-switch-env size [size 1] true [1 size] 
                          (make-random-switch-set size size n-switches seed))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn nav-outcome-map [s dx dy xc yc]
  (let [cx (env/get-var s '[x])
        cy (env/get-var s '[y])]
    {(env/set-var (env/set-var s '[x] dx) '[y] dy)
     (+ (* xc (util/abs (- dx cx))) (* yc (util/abs (- dy cy))))}))

(defn exact-nav-map [s dx dy]
  (let [[xc yc] (if (env/get-var s '[h]) [-2 -4] [-4 -2])]
    (nav-outcome-map s dx dy xc yc)))

(deftype SimpleNavHLA [dx dy] :as this
  env/Action                (action-name [] ['nav dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (if (and (= dx (env/get-var s '[x])) 
                                      (= dy (env/get-var s '[y])))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)] :when a]
                                 [a this])))
                            (cycle-level- [s] 1)
  env/AngelicAction         (optimistic-map- [s] (exact-nav-map s dx dy))
                            (pessimistic-map-[s] (exact-nav-map s dx dy)))

(deftype NavDHLA [h? dest] :as this
  env/Action                (action-name [] [(if h? 'navh 'navv) dest])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] (if h? '#{[x] [h]} '#{[y] [h]}))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (if (= dest (env/get-var s (if h? '[x] '[y]))) 
                                 [[]]
                               (for [af (if h? [make-left make-right] [make-up make-down])
                                     :let [a (af s)] :when a]
                                 [a this])))
                            (cycle-level- [s] 1)
  env/AngelicAction         (optimistic-map- [s]
                              (let [dir  (if h? '[x] '[y])
                                    cur  (env/get-var s dir)
                                    cost (if (util/truth= (env/get-var s '[h]) h?) -2 -4)]
                                {(env/set-var s dir dest)
                                 (* cost (util/abs (- cur dest)))}))
                            (pessimistic-map-[s] (env/optimistic-map- this s)))

(deftype SplitNavHLA [dx dy] 
  env/Action                (action-name [] ['split-nav dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [s] [[(NavDHLA true dx) (NavDHLA false dy)]])
                            (cycle-level- [s] nil)
  env/AngelicAction         (optimistic-map- [s] (exact-nav-map s dx dy))
                            (pessimistic-map-[s] (exact-nav-map s dx dy)))



(deftype NavSwitchTLA [switch-set gx gy nav-factory] :as this
  env/Action                (action-name [] '[top])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (cons [(nav-factory gx gy)]
                               (for [[sx sy] switch-set]
                                 [(nav-factory sx sy)
                                  (make-specific-switch (env/get-var s '[h]) sx sy)
                                  this]))) 
                            (cycle-level- [s] 2)
  env/AngelicAction         (optimistic-map- [s] (nav-outcome-map s gx gy 2 2))
                            (pessimistic-map-[s] (exact-nav-map s gx gy)))


(defn make-nav-switch-tla [env split-nav?]
  (NavSwitchTLA (:switch-set env) (:gx env) (:gy env)
                (if split-nav?  SplitNavHLA SimpleNavHLA)))

(defn make-nav-switch-hierarchy [#^NavSwitchEnv env split-nav?]
  (hierarchy/SimpleHierarchicalEnv env [(make-nav-switch-tla env split-nav?)]))


