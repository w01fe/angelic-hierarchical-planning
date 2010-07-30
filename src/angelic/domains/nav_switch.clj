(ns angelic.domains.nav-switch
  (:require [edu.berkeley.ai.util :as util]
            [angelic [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util Random]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-dir [s name h? dir]
  (let [dim   (if h? '[x] '[y])
        cur-h (state/get-var s '[h])
        ov    (state/get-var s dim)
        nv    (+ ov dir)]
    (when (<= 1 nv (get (state/get-var s :const) dim))
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
  (let [cur-h (state/get-var s '[h])
        cur-x (state/get-var s '[x])
        cur-y (state/get-var s '[y])]
    (when (contains? (get (state/get-var s :const) :switch-set) [cur-x cur-y])
      (make-specific-switch cur-h cur-x cur-y))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Env ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord NavSwitchEnv [width height sx sy sh? gx gy switch-set] 
  env/Env
  (initial-state [_] 
    {'[x] sx '[y] sy '[h] (if sh? true false)
     :const {'[x] width '[y] height :switch-set switch-set}})
  (actions-fn [_]
   (fn nav-switch-actions [s]
     (filter identity (map #(% s) [make-left make-right make-up make-down make-switch]))))
  (goal-fn [this] 
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
  (let [cx (state/get-var s '[x])
        cy (state/get-var s '[y])]
    {(state/set-var (state/set-var s '[x] dx) '[y] dy)
     (+ (* xc (util/abs (- dx cx))) (* yc (util/abs (- dy cy))))}))

(defn exact-nav-map [s dx dy]
  (let [[xc yc] (if (state/get-var s '[h]) [-2 -4] [-4 -2])]
    (nav-outcome-map s dx dy xc yc)))

(defrecord SimpleNavHLA [dx dy]
  env/Action 
               (action-name [_] ['nav dx dy])
                            (primitive? [_] false)
  env/ContextualAction      (precondition-context [_ s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [_ s]
                             (if (and (= dx (state/get-var s '[x])) 
                                      (= dy (state/get-var s '[y])))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)] :when a]
                                 [a this])))
                            (cycle-level- [_ s] 1)
  hierarchy/ExplicitAngelicAction         (optimistic-map- [_ s] (exact-nav-map s dx dy))
                            (pessimistic-map- [_ s] (exact-nav-map s dx dy)))

(deftype NavDHLA [h? dest] :as this
  env/Action                (action-name [_] [(if h? 'navh 'navv) dest])
                            (primitive? [_] false)
  env/ContextualAction      (precondition-context [_ s] (if h? '#{[x] [h]} '#{[y] [h]}))
  hierarchy/HighLevelAction (immediate-refinements- [_ s]
                              (if (= dest (state/get-var s (if h? '[x] '[y]))) 
                                 [[]]
                               (for [af (if h? [make-left make-right] [make-up make-down])
                                     :let [a (af s)] :when a]
                                 [a this])))
                            (cycle-level- [_ s] 1)
  hierarchy/ExplicitAngelicAction         (optimistic-map- [_ s]
                              (let [dir  (if h? '[x] '[y])
                                    cur  (state/get-var s dir)
                                    cost (if (util/truth= (state/get-var s '[h]) h?) -2 -4)]
                                {(state/set-var s dir dest)
                                 (* cost (util/abs (- cur dest)))}))
                            (pessimistic-map- [_ s] (env/optimistic-map- this s)))

(deftype SplitNavHLA [dx dy] 
  env/Action                (action-name [_] ['split-nav dx dy])
                            (primitive? [_] false)
  env/ContextualAction      (precondition-context [_ s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [_ s] [[(NavDHLA true dx) (NavDHLA false dy)]])
                            (cycle-level- [_ s] nil)
  hierarchy/ExplicitAngelicAction         (optimistic-map- [_ s] (exact-nav-map s dx dy))
                            (pessimistic-map- [_ s] (exact-nav-map s dx dy)))



(deftype NavSwitchTLA [switch-set gx gy nav-factory] :as this
  env/Action                (action-name [_] '[top])
                            (primitive? [_] false)
  env/ContextualAction      (precondition-context [_ s] '#{[x] [y] [h]})
  hierarchy/HighLevelAction (immediate-refinements- [_ s]
                             (cons [(nav-factory gx gy)]
                               (for [[sx sy] switch-set]
                                 [(nav-factory sx sy)
                                  (make-specific-switch (state/get-var s '[h]) sx sy)
                                  this]))) 
                            (cycle-level- [_ s] 2)
  hierarchy/ExplicitAngelicAction         (optimistic-map- [_ s] (nav-outcome-map s gx gy 2 2))
                            (pessimistic-map- [_ s] (exact-nav-map s gx gy)))


(defn make-nav-switch-tla [env split-nav?]
  (NavSwitchTLA (:switch-set env) (:gx env) (:gy env)
                (if split-nav?  SplitNavHLA SimpleNavHLA)))

(defn make-nav-switch-hierarchy [#^NavSwitchEnv env split-nav?]
  (hierarchy/SimpleHierarchicalEnv env [(make-nav-switch-tla env split-nav?)]))


