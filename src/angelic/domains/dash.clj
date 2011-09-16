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

;; States correspond to bit strings.
;; The goal is to hide a fixed number of ones in a string of zeros.
;; Costs increase as you go.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Primitives ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn next-bit [[sp i]] [sp (inc i)])

(defn- make-skip [env bit]
  (env-util/make-factored-primitive
   [:skip bit]
   {[:bit] bit}
   {[:bit] (next-bit bit)}
   (-> env :base-rews (get (second bit)))))

(defn- make-set [env bit cnt]
  (env-util/make-factored-primitive
   [:set bit cnt]
   {[:bit] bit [:count] cnt}
   {[:bit] (next-bit bit) [:count] (inc cnt) bit 1}
   (+ (-> env :base-rews (get (second bit)))
      (-> env :set-rews (get (second bit))))))

(defn- make-next [env sp]
  (env-util/make-factored-primitive
   [:next sp]
   {[:bit] [sp (-> env :base-rews count)]
    [:count] (-> env :target-count)}
   {[:bit] [(inc sp) 0]
    [:count] 0}
   0))

(defn simple-dash-heuristic [{:keys [nsp nv target-count window-lb] :as env} w s]
  (let [[csp ci] (state/get-var s [:bit])
        cnt (state/get-var s [:count])]
    (if (< (- nv ci) (- target-count cnt))
      Double/NEGATIVE_INFINITY
      (* w
         (+ (* (- nsp csp 1) (window-lb 0 nv target-count))
            (window-lb ci nv (- target-count cnt)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Env ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nv = (expt 2 depth)
(defrecord DashEnv [nsp depth nv target-count base-rews set-rews window-lb]
  env/Env
  (initial-state [e]
    (into {[:bit] [0 0] [:count] 0}
          (for [sp (range nsp)
                v  (range nv)]
            [[sp v] 0])))
  (actions-fn    [e]
    (fn dash-actions [s]
      (let [[csp cv :as bit] (state/get-var s [:bit])
            cnt (state/get-var s [:count])]
        (when (< csp nsp)
          (if (= cv nv)
            [(make-next e csp)]
            (cons
             (make-skip e bit)
             (when (< cnt target-count)
               [(make-set e bit cnt)])))))))
  (goal-fn       [e] 
    (let [goal-map (env/goal-map e)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))

  env/FactoredEnv
  (goal-map      [_] {'[:bit] [nsp 0]}))


;; Allowing to run dry, not set enough bits.
(defn make-dash-env
  ([nsp depth target-count]
     (let [nv (util/expt 2 depth)]
       (make-dash-env nsp depth target-count (repeat nv -1) (take nv (iterate dec -1)))))
  ([nsp depth target-count base-rews set-rews]
     (assert (= (util/expt 2 depth) (count base-rews) (count set-rews)))
     (assert (every? neg? (concat base-rews set-rews)))
     (let [base-rews (vec base-rews) set-rews (vec set-rews)]
       (DashEnv. nsp depth (count base-rews) target-count base-rews set-rews
                 (memoize
                  (fn [start end set-cnt]
                    (->> (subvec set-rews start end)
                         sort 
                         (take-last set-cnt)
                         (concat (subvec base-rews start end))
                         (reduce +))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(declare make-dash)

(defn depth [env start end]
  (- (:depth env) (Integer/numberOfTrailingZeros (int (- end start)))))

(defn dash-pc [sp start end]
  (set (concat [[:count] [:bit]] (for [i (range start end)] [sp i]))))

(defn implicit-dash-opt [ss env sp start end prev-count target-count level-weight]
  (assert (= (state/get-var ss [:count]) #{prev-count}))
  (assert (= (state/get-var ss [:bit]) #{[sp start]}))    
  [(state/set-vars
    ss
    (concat [[[:bit] #{[sp end]}] [[:count] #{(+ prev-count target-count)}]]
            (for [i (range start end)]
              [[sp i] #{0 1}])))
   (* (level-weight (depth env start end))
      ((:window-lb env) start end target-count))])

(defn dash-successors [s vs dash w]
  ((fn succs [s vs c]
     (if-let [[fv & rvs] (seq vs)]
       (concat
        (succs (state/set-var s fv 0) rvs (+ c 1))
        (succs (state/set-var s fv 1) rvs (+ c 2)))
       [[s (* -1 w c)]]))
   (state/set-var s [:current] (next-current (last vs)))
   vs dash))

(defn explicit-dash-opt [s env sp start end prev-count target-count level-weight]
  (assert (= (state/get-var s [:count]) prev-count))
  (assert (= (state/get-var s [:bit]) [sp start]))
  (into {}
        (for [is (util/combinations (range start end) target-count)]
          [(state/set-vars
            s
            (concat [[[:bit] [sp end]] [[:count] (+ prev-count target-count)]]
              (for [i is]
                [[sp i] 1])))
           (* (level-weight (depth env start end))
              (reduce + ((:window-lb env) start end 0)
                      (map (:set-rews env) is)))])))




(defrecord DashHLA [env sp start end prev-count target-count level-weight] 
  env/Action
  (action-name [_] [:dash [sp [start end]] prev-count target-count])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (dash-pc sp start end))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [window (/ (- end start) 2)]
      (assert (integer? window))
      (for [tc1 (range (inc target-count))
            :let [tc2 (- target-count tc1)]
            :when (and (<= 0 tc1 window) (<= 0 tc2 window))]
        [(make-dash env sp start (+ start window) prev-count tc1 level-weight)
         (make-dash env sp (+ start window) end (+ prev-count tc1) tc2 level-weight)]))) 
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s] (explicit-dash-opt s env sp start end prev-count target-count level-weight))
  (pessimistic-map- [_ s] nil)

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] (dash-pc sp start end))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a :dummy)] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (implicit-dash-opt ss env sp start end prev-count target-count level-weight))
  (pessimistic-set-and-reward- [a ss] nil))

(defn make-dash [env sp start end prev-count target-count level-weight]
  (if (= end (inc start))
    (if (> target-count 0)
      (make-set env [sp start] prev-count)
      (make-skip env [sp start]))
    (DashHLA. env sp start end prev-count target-count level-weight)))



(defrecord DashTLA [env level-weight finish-state] 
  env/Action
  (action-name [_] [:dash-tla])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] (set (state/list-vars s)))

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [{:keys [nsp nv target-count]} env]
      [(concat
        (apply concat (for [sp (range nsp)]
                        [(make-dash env sp 0 nv 0 target-count level-weight)
                         (make-next env sp)]))
        [(env-util/make-finish-action env)])])) 
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


(defn make-dash-hierarchy
  [^DashEnv env level-weight]
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(DashTLA. env level-weight (env-util/make-finish-goal-state env))]))




  ;; actually want something that splits cost.
  ;; First bit decides first bit of cost.
  ;; next two bits
  ;; 1 1 2 1 1 2 4 1 1 2 1 1 2 4
  ;; 1 1 2 1 1 2 8 1 1 2 1 1 2 8 32