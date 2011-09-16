(ns angelic.domains.dash
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))

;; A domain engineered to make all algorithms besides DASH-A* weep.

;; States correspond to bit strings, and the costs to reach them are n + count(one bits)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- make-bit [sp v b]
  (env-util/make-factored-primitive
   [:bit sp v b]
   {[:current] [sp v]}
   {[:current] [sp (inc v)]
    [sp v] b}
   (case b 0 -1 1 -2)))

(defn- make-next [sp nv]
  (env-util/make-factored-primitive
   [:next sp]
   {[:current] [sp nv]}
   {[:current] [(inc sp) 0]}
   0))

(defn simple-dash-heuristic [w s]
  (let [{:keys [nsp nv]} (state/get-var s :const)
        [csp cv] (state/get-var s [:current])]
    (* -1 w
       (+ (* nv (- nsp csp 1))
          (- nv cv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Env ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nv = (expt 2 depth)
(defrecord DashEnv [nsp depth nv]
  env/Env
  (initial-state [_]
    (into {[:current] [0 0] :const {:nsp nsp :depth depth :nv nv}}
          (for [sp (range nsp)
                v  (range nv)]
            [[sp v] 0])))
  (actions-fn    [_]
    (fn dash-actions [s]
      (let [[csp cv] (state/get-var s [:current])]
        (when (< csp nsp)
          (if (= cv nv)
            [(make-next csp nv)]
            [(make-bit csp cv 0) (make-bit csp cv 1)])))))
  (goal-fn       [this] 
    (let [goal-map (env/goal-map this)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))

  env/FactoredEnv
  (goal-map      [_] {'[:current] [nsp 0]}))


(defn make-dash-env [nsp depth]
  (DashEnv. nsp depth (util/expt 2 depth)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Parity hierarchy.
;; Should really rule out states with wrong parity, but it's optimistic so it's OK.

(declare make-parity)

(defn bit-count [x] (Integer/bitCount (int x)))

(defn dash-vars [sp i d max-depth]
  (let [r (util/expt 2 (- max-depth d))]
   (for [x (range r)]
     [sp (+ (* i r) x)])))

(defn dash-pc [sp i d max-depth]
  (set (cons [:current] (dash-vars sp i d max-depth))))

(defn next-current [[sp i]] [sp (inc i)])


(defn implicit-parity-opt [ss sp i d max-depth parity level-weight]
  (let [vs (dash-vars sp i d max-depth)]
    [(state/set-vars ss (cons [[:current] #{(next-current (last vs))}] (for [v vs] [v #{0 1}])))
     (* (level-weight d) (- 0 parity (count vs)))]))

(defn parity-successors [s vs parity w]
  ((fn succs [s vs c]
     (if-let [[fv & rvs] (seq vs)]
       (concat
        (succs (state/set-var s fv 0) rvs (+ c 1))
        (succs (state/set-var s fv 1) rvs (+ c 2)))
       [[s (* -1 w c)]]))
   (state/set-var s [:current] (next-current (last vs)))
   vs parity))

(defn explicit-parity-opt [s sp i d max-depth parity level-weight]
  (into {} (parity-successors s (dash-vars sp i d max-depth) parity (level-weight d))))




(defrecord ParityHLA [sp i d max-depth parity level-weight] 
  env/Action
  (action-name [_] [:dash-main sp i d parity])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (dash-pc sp i d max-depth))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    [[(make-parity sp (* 2 i) (inc d) max-depth 0 level-weight)
      (make-parity sp (inc (* 2 i)) (inc d) max-depth parity level-weight)]
     [(make-parity sp (* 2 i) (inc d) max-depth 1 level-weight)
      (make-parity sp (inc (* 2 i)) (inc d) max-depth (- 1 parity) level-weight)]]) 
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s] (explicit-parity-opt s sp i d max-depth parity level-weight))
  (pessimistic-map- [_ s] nil)

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] (dash-pc sp i d max-depth))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (implicit-parity-opt ss sp i d max-depth parity level-weight))
  (pessimistic-set-and-reward- [a ss] nil))

(defn make-parity [sp i d max-depth parity level-weight]
  (if (= d max-depth)
    (make-bit sp i parity)
    (ParityHLA. sp i d max-depth parity level-weight)))




(defrecord ParitySPHLA [sp nv max-depth level-weight] 
  env/Action
  (action-name [_] [:dash-sp sp])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (dash-pc sp 0 0 max-depth))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    [[(make-parity sp 0 0 max-depth 0 level-weight)
      (make-next sp nv)]
     [(make-parity sp 0 0 max-depth 1 level-weight)
      (make-next sp nv)]]) 
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s]
    (util/map-keys #(state/set-var % [:current] [(inc sp) 0])
                   (explicit-parity-opt s sp 0 0 max-depth 0 level-weight)))
  (pessimistic-map- [_ s] nil)

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] (dash-pc sp 0 0 max-depth))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (update-in
     (implicit-parity-opt ss sp 0 0 max-depth 0 level-weight)
     [0] state/set-var [:current] #{[(inc sp) 0]}))
  (pessimistic-set-and-reward- [a ss] nil))




(defrecord ParityTLA [env nsp nv depth level-weight finish-state] 
  env/Action
  (action-name [_] [:dash-tla])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (set (state/list-vars s)))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    [(concat
      (for [sp (range nsp)] (ParitySPHLA. sp nv depth level-weight))
      [(env-util/make-finish-action env)])]) 
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s] {(state/set-vars s finish-state) 0})
  (pessimistic-map- [_ s] nil)

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] (set (state/list-vars ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    [(state/set-vars ss (util/map-vals (fn [x] #{x}) finish-state)) 0])
  (pessimistic-set-and-reward- [a ss] nil))
 

(defn make-parity-hierarchy
  [^DashEnv env level-weight]
  (let [{:keys [nsp depth nv]} env]
    (hierarchy-util/make-simple-hierarchical-env
     env
     [(ParityTLA. env nsp nv depth level-weight (env-util/make-finish-goal-state env))])))




;; actually want something that splits cost.
;; First bit decides first bit of cost.
;; next two bits 