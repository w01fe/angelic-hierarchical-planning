(ns angelic.domains.tav
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))

;; Encoding of TAV-like inference (Chatterjee et al. ) as angelic search problem

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Edges ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-edge [type level from to start end]
  (assert (#{:normal :re-entry} type))
  {:type type :level level :from from :to to :start start :end end})

(defn state-children [l s]
  (assert (> l 0))
  [(* 2 s) (inc (* 2 s))])

(defn state-sibling [l s]
  (bit-xor s 1))

(defn mid-time [start end]
  (quot (inc (+ start end)) 2))

(defn primitive-edge? [e]
  (let [{:keys [type level from to start end]} e]
    (and (zero? level) (or (and (= type :normal) (= from to)) (= end (inc start))))))

(defn edge-type [e]
  (case (:type e)
        :re-entry :re-entry
        (if (= (:from e) (:to e))
          :direct
          :cross)))

(defn make-edges [level from to start end]
  (if (= from to)
    (for [t (cons :normal (when (> end (inc start)) [:re-entry]))]
      (make-edge t level from to start end))
    [(make-edge :normal level from to start end)]))

(defn edge-children [e]
  (let [{:keys [level from to start end]} e]
    (case (edge-type e)
      :direct   (let [scs (state-children level from)]
                  (for [sc1 scs, sc2 scs, e (make-edges (dec level) sc1 sc2 start end)] [e]))
      :re-entry (let [mid (mid-time start end)
                      sib (state-sibling level from)]
                  (cons
                   [(make-edge :normal level from sib start mid)
                    (make-edge :normal level sib from mid end)]
                   (for [h1 (make-edges level from from start mid)
                         h2 (make-edges level from from mid end)
                         :when (not (and (= :normal (:type h1)) (= :normal (:type h2))))]
                     [h1 h2])))
      :cross    (if (= end (inc start))
                  (for [sc1 (state-children level from)
                        sc2 (state-children level to)]
                    [(make-edge :normal (dec level) sc1 sc2 start end)])
                  (let [mid (mid-time start end)]
                   (assert (= from (state-sibling level to)))
                   (concat
                    (for [h1 (make-edges level from from start mid)]
                      [h1 (make-edge :normal level from to mid end)])
                    (for [h2 (make-edges level to to mid end)]
                      [(make-edge :normal level from to start mid) h2])))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Reading scores ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn log2 [x]
  (if (= x 1)
    0
    (do (assert (= (mod x 2) 0))
        (inc (log2 (quot x 2))))))

(defn reads-string [s]
  (read-string (str "[" s "]")))

(defn read-direct-line [max-level l]
  (let [[level state start end score] (reads-string l)]
    [(make-edge :normal (- max-level level) (dec state) (dec state) (dec start) (dec end)) score]))

(defn read-other-line [max-level l]
  (let [[level from to start end score] (reads-string l)]
    [(make-edge (if (= from to) :re-entry :normal) (- max-level level)
                (dec from) (dec to) (dec start) (dec end)) score]))

(defn read-tav-files [stem S T]
  (let [max-level (log2 S)
        m (into {}
                (concat
                 (map (partial read-direct-line max-level)
                      (drop 3 (util/read-lines (str stem "d.txt"))))
                 (map (partial read-other-line max-level)
                      (drop 3 (util/read-lines (str stem "o.txt"))))))]
    (into m
          (cons
           [(make-edge :normal max-level 0 0 0 T)
            (max (get m (make-edge :normal   (dec max-level) 0 0 0 T))
                 (get m (make-edge :normal   (dec max-level) 1 1 0 T))
                 (get m (make-edge :normal   (dec max-level) 0 1 0 T))
                 (get m (make-edge :normal   (dec max-level) 1 0 0 T))
                 (get m (make-edge :re-entry (dec max-level) 0 0 0 T))
                 (get m (make-edge :re-entry (dec max-level) 1 1 0 T)))]
           (for [l (range 0 (inc max-level))
                 s (range (util/expt 2 (- max-level l)))]
             [(make-edge :normal l 0 s -1 0) 0.0])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Env ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn- make-primitive [[{:keys [level from to start end]} reward]]
  (assert (zero? level))
  (env-util/make-factored-primitive
   [:normal 0 [from to] [start end]]
   #_(if (= end (inc start)) [to] [to :jump end])
   {'[s] from '[t] start}
   {'[s] to   '[t] end}
   reward))



(defrecord TAVEnv [S T edges]
  env/Env
  (initial-state [_]
    {'[s] 0 '[t] -1})
  (actions-fn    [_]
    (fn nav-switch-actions [state]
      (let [s (state/get-var state '[s])
            t (state/get-var state '[t])]
        (for [ss (range S)]
          (make-primitive (find edges (make-edge :normal 0 s ss t (inc t))))))))
  (goal-fn       [this] 
    (let [goal-map (env/goal-map this)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))

  env/FactoredEnv
  (goal-map      [_] {'[t] T}))

(defonce demo-tav-files (read-tav-files "/Users/w01fe/Projects/angel/problems/tav/0" 16 100))
(defn make-demo-tav-env
  ([] (make-demo-tav-env 16 100))
  ([s t] (TAVEnv. s t demo-tav-files)))

(def demo-tav-env (make-demo-tav-env))
(def small-demo-tav-env (make-demo-tav-env 16 100))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchies ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def make-state-set
  (memoize (fn [l s] (let [b (util/expt 2 l)] (set (range (* s b) (* (inc s) b)))))))

(declare make-tav-action)
(def edge-map)

;; TODO: we do actually need to take input state constraints into account.
;; Also, need to handle initial action in the hierarchy somehow. 

(defrecord TAVHLA [#_ edge-map edge]
  env/Action 
  (action-name [_] [(:type edge) (:level edge) [(:from edge) (:to edge)] [(:start edge) (:end edge)]])
  (primitive?  [_] false)

  angelic/ImplicitAngelicAction
  (precondition-context-set [_ ss] '#{[s] [t]})
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [c (edge-children edge)
          :when (seq (util/intersection (state/get-var ss '[s])
                                        (make-state-set (:level (first c)) (:from (first c)))))]
      [nil (map (partial make-tav-action edge-map) c)]))
  (optimistic-set-and-reward- [a ss]
    (util/assert-is (= (state/get-var ss '[t]) #{(:start edge)}))
;   (util/assert-is (= (state/get-var ss '[s]) (make-state-set (:level edge) (:from edge))))
    (when (seq (util/intersection (state/get-var ss '[s]) (make-state-set (:level edge) (:from edge))))
     [(state/set-vars ss [['[s] (make-state-set (:level edge) (:to edge))] ['[t] #{(:end edge)}]])
      (get edge-map edge)]))
  (pessimistic-set-and-reward- [a ss] nil))

(defn make-tav-action [edge-map edge]
  (if (primitive-edge? edge)
    (make-primitive (find edge-map edge))
    (TAVHLA. #_ edge-map edge)))

;; This init is a bit hacky but should work?
(defn make-tav-hierarchy [^TAVEnv env]
  (def edge-map (:edges env))
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(hierarchy-util/make-top-level-action
     env
      (for [s (range (:S env))]
        [(make-primitive (find (:edges env) (make-edge :normal 0 0 s -1 0)))
         (TAVHLA. #_ (:edges env) (make-edge :normal (log2 (:S env)) 0 0 0 (:T env)))])
      0.0)]))

;; #_(TAVHLA. #_ (:edges env) (make-edge :normal (log2 (:S env)) 0 0 -1 0))

(def demo-tav-hierarchy (make-tav-hierarchy demo-tav-env))
(def small-demo-tav-hierarchy (make-tav-hierarchy small-demo-tav-env))


;; (run-counted #(uniform-cost-search demo-tav-env))

;; (require '[ angelic.search.implicit.dash-astar-opt :as dao] )
;;(dao/implicit-dash-a*-opt demo-tav-hierarchy)

;; (->> (uniform-cost-search angelic.domains.tav/small-demo-tav-env) first (map (comp second first)))