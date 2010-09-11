(ns angelic.domains.nav-switch
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- make-dir [s name h? dir]
  (let [dim   (if h? '[x] '[y])
        cur-h (state/get-var s '[h])
        ov    (state/get-var s dim)
        nv    (+ ov dir)]
    (when (<= 1 nv (get (state/get-var s :const) dim))
      (env-util/make-factored-primitive name {dim ov, '[h] cur-h} {dim nv} 
                             (if (util/truth= cur-h h?) -2 -4)))))

(defn- make-left  [s] (make-dir s '[left]  true  -1))
(defn- make-right [s] (make-dir s '[right] true   1))
(defn- make-up    [s] (make-dir s '[up]    false  1))
(defn- make-down  [s] (make-dir s '[down]  false -1))


(defn- make-specific-switch [cur-h cur-x cur-y]
  (env-util/make-factored-primitive 
   [(if cur-h 'v 'h)] {'[h] cur-h '[x] cur-x '[y] cur-y} {'[h] (not cur-h)} -1))


(defn- make-switch [s]
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
     :const {'[x] width '[y] height :switch-set (util/to-set switch-set)}})
  (actions-fn    [_]
   (fn nav-switch-actions [s]
     (filter identity (map #(% s) [make-left make-right make-up make-down make-switch]))))
  (goal-fn       [this] 
    (let [goal-map (env/goal-map this)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))

  env/FactoredEnv
  (goal-map      [_] {'[x] gx '[y] gy}))

(defn make-random-switch-set [width height n seed]
  (let [r (Random. (long seed))
        width (int width) height (int height)]
    (.nextDouble r) (.nextDouble r)    
    (set (take n (distinct (repeatedly #(vector (inc (.nextInt r width)) 
                                                (inc (.nextInt r height)))))))))

(defn make-nav-switch-env [size [sx sy] init-h [gx gy] switch-set]
  (NavSwitchEnv. size size sx sy init-h gx gy switch-set))

(defn make-random-nav-switch-env 
  ([size n-switches] 
     (make-random-nav-switch-env size n-switches (rand-int 10000000)))
  ([size n-switches seed]
     (make-nav-switch-env size [size 1] true [1 size] 
                          (make-random-switch-set size size n-switches seed))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- nav-outcome-map [s dx dy xc yc]
  (let [cx (state/get-var s '[x])
        cy (state/get-var s '[y])]
    {(state/set-var (state/set-var s '[x] dx) '[y] dy)
     (+ (* xc (util/abs (- dx cx))) (* yc (util/abs (- dy cy))))}))

(defn- exact-nav-map [s dx dy]
  (let [[xc yc] (if (state/get-var s '[h]) [-2 -4] [-4 -2])]
    (nav-outcome-map s dx dy xc yc)))

(defn nav-reward-from-set [ss dx dy combiner]
  (let [cx (util/safe-singleton (state/get-var ss '[x]))
        cy (util/safe-singleton (state/get-var ss '[y]))]
    (apply combiner
           (for [h? (state/get-var ss '[h])
                 :let [[xc yc] (if h? [-2 -4] [-4 -2])]]
             (+ (* xc (util/abs (- dx cx))) (* yc (util/abs (- dy cy))))))))

(defn nav-set-and-reward [ss dx dy combiner]
  [(state/set-vars ss [['[x] #{dx}] ['[y] #{dy}]])
   (nav-reward-from-set ss dx dy combiner)])

(defrecord SimpleNavHLA [dx dy]
  env/Action 
  (action-name [_] ['nav dx dy])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] '#{[x] [y] [h]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (and (= dx (state/get-var s '[x])) 
             (= dy (state/get-var s '[y])))
      [[]]
      (for [af [make-left make-right make-up make-down]
            :let [a (af s)] :when a]
        [a this])))
  (cycle-level- [_ s] 1)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s] (exact-nav-map s dx dy))
  (pessimistic-map- [_ s] (exact-nav-map s dx dy))

  angelic/ImplicitAngelicAction
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]  (nav-set-and-reward ss dx dy max))
  (pessimistic-set-and-reward- [a ss] (nav-set-and-reward ss dx dy max)))


(defn nav-d-set-and-reward [ss h? dest combiner]
  (let [dir  (if h? '[x] '[y])
        cur  (state/get-var ss dir)]
    [(state/set-var ss dir #{dest})
     (apply combiner
            (for [ch? (state/get-var ss '[h])]
              (* (if (util/truth= ch? h?) -2 -4) (util/abs (- cur dest)))))]))

(defrecord NavDHLA [h? dest]
  env/Action
  (action-name [_] [(if h? 'navh 'navv) dest])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (if h? '#{[x] [h]} '#{[y] [h]}))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (= dest (state/get-var s (if h? '[x] '[y]))) 
      [[]]
      (for [af (if h? [make-left make-right] [make-up make-down])
            :let [a (af s)] :when a]
        [a this])))
  (cycle-level-           [_ s] 1)
  
  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s]
    (let [dir  (if h? '[x] '[y])
          cur  (state/get-var s dir)
          cost (if (util/truth= (state/get-var s '[h]) h?) -2 -4)]
      {(state/set-var s dir dest)
       (* cost (util/abs (- cur dest)))}))
  (pessimistic-map- [this s] (angelic/optimistic-map- this s))

  angelic/ImplicitAngelicAction
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss] (nav-d-set-and-reward ss h? dest max))
  (pessimistic-set-and-reward- [a ss] (nav-d-set-and-reward ss h? dest min)))



(defrecord SplitNavHLA [dx dy] 
  env/Action
  (action-name [_] ['split-nav dx dy])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] '#{[x] [y] [h]})

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s] [[(NavDHLA. true dx) (NavDHLA. false dy)]])
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s] (exact-nav-map s dx dy))
  (pessimistic-map- [_ s] (exact-nav-map s dx dy))

  angelic/ImplicitAngelicAction
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]  (nav-set-and-reward ss dx dy max))
  (pessimistic-set-and-reward- [a ss] (nav-set-and-reward ss dx dy min)))

; Does not work with null vals
(defn merge-map-keys [map-fn merge-fn m]
  (loop [remaining-kv m
         result (transient {})]
    (if-let [[[k v] & r] (seq remaining-kv)]
      (let [nk (map-fn k)]
        (recur r (assoc! result nk (if-let [ov (get result nk)] (merge-fn v ov) v))))      
      (persistent! result))))



(defrecord NavSwitchTLA [env switch-set gx gy nav-factory finish] 
  env/Action
  (action-name [_] '[top])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] '#{[x] [y] [h]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (cons [(nav-factory gx gy) (env-util/make-finish-action env)]
          (for [[sx sy] switch-set]
            [(nav-factory sx sy)
             (make-specific-switch (state/get-var s '[h]) sx sy)
             this]))) 
  (cycle-level- [_ s] 2)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s] (merge-map-keys #(state/set-vars % finish) max (nav-outcome-map s gx gy 2 2)))
  (pessimistic-map- [_ s] (merge-map-keys #(state/set-vars % finish) max (exact-nav-map s gx gy)))

  angelic/ImplicitAngelicAction
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    [(state/set-vars ss (util/map-vals (fn [x] #{x}) finish))
     (* -2 (+ (- gx (util/safe-singleton (state/get-var ss '[x])))
              (- gy (util/safe-singleton (state/get-var ss '[y])))))])
  (pessimistic-set-and-reward- [a ss]
    [(state/set-vars ss (util/map-vals (fn [x] #{x}) finish))
     (nav-reward-from-set ss gx gy min)]))


(defn- make-nav-switch-tla [env split-nav?]
  (NavSwitchTLA. env (:switch-set env) (:gx env) (:gy env)
                 (if split-nav?  #(SplitNavHLA. %1 %2) #(SimpleNavHLA. %1 %2))
                 (env-util/make-finish-goal-state env)))

(defn make-nav-switch-hierarchy [#^NavSwitchEnv env split-nav?]
  (hierarchy-util/make-simple-hierarchical-env env [(make-nav-switch-tla env split-nav?)]))


