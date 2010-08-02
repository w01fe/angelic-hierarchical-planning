(ns angelic.hierarchy.angelic
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.util :as env-util]
            [angelic.env.state :as state]            
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set] ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; Explicit angelic actions ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: better to have single map from state to range ?
(defprotocol ExplicitAngelicAction
  (optimistic-map- [a s])
  (pessimistic-map- [a s]))

(defn optimistic-map [a s]
  (util/sref-set! hierarchy/*optimistic-counter* (inc (util/sref-get hierarchy/*optimistic-counter*)))
  (optimistic-map- a s))

(defn pessimistic-map [a s]
  (util/sref-set! hierarchy/*pessimistic-counter* (inc (util/sref-get hierarchy/*pessimistic-counter*)))
  (pessimistic-map- a s))

(extend angelic.env.util.FactoredPrimitive
  ExplicitAngelicAction
  {:optimistic-map- 
     (fn optimistic-map- [this s]
       (if (env/applicable? this s) 
         (let [[s r] (env/next-state-and-reward this s)] {s r}) 
         {}))
   :pessimistic-map- 
     (fn pessimistic-map- [this s]
       (if (env/applicable? this s) 
         (let [[s r] (env/next-state-and-reward this s)] {s r}) 
         {}))})

(defn next-explicit-map-and-reward-bounds [a state]
  (let [opt  (optimistic-map a state)
        pess (pessimistic-map a state)]
    (into {} (for [[s r] opt] [s [(get pess s Double/NEGATIVE_INFINITY) r]]))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implicit angelic actions ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol ImplicitAngelicAction
  (can-refine-from-set? [a ss] "Return true if set has enough information to refine.")
  (immediate-refinements-set- [a ss] "Return seq of [constraint ref] pairs from this set")
  (optimistic-set-and-reward- [a ss] "Return pair of implicit outcome set and reward, or nil")
  (pessimistic-set-and-reward- [a ss] "Return pair of implicit outcome set and reward, or nil"))

(defn immediate-refinements-set [a ss]  
  ;(println "Refs for " (env/action-name a) "from" (map #(state/get-var s %) '[[atx] [aty]]))
  (util/timeout)
  (let [refs (immediate-refinements-set- a ss)]
    (util/sref-set! hierarchy/*ref-counter*  (+ 1            (util/sref-get hierarchy/*ref-counter*)))
    (util/sref-set! hierarchy/*plan-counter* (+ (count refs) (util/sref-get hierarchy/*plan-counter*)))
    refs))

(defn optimistic-set-and-reward [a ss]
  (util/sref-set! hierarchy/*optimistic-counter* (inc (util/sref-get hierarchy/*optimistic-counter*)))
  (optimistic-set-and-reward- a ss))

(defn pessimistic-set-and-reward [a ss]
  (util/sref-set! hierarchy/*pessimistic-counter* (inc (util/sref-get hierarchy/*pessimistic-counter*)))
  (pessimistic-set-and-reward- a ss))

(defn next-implicit-set-and-reward-bounds
  "Return [set [pess-rew opt-rew]] or nil, asserting that pess and opt have same set."
  [a ss]
  (when-let [[opt-set opt-rew] (optimistic-set-and-reward a ss)]
    (let [[pess-set pess-rew] (or (pessimistic-set-and-reward a ss) [opt-set Double/NEGATIVE_INFINITY])]
      (assert (= opt-set pess-set))
      [opt-set [pess-rew opt-rew]])))

(extend angelic.env.util.FactoredPrimitive
  ImplicitAngelicAction
  (let [exact
        (fn exact-set-and-reward- [this ss]
          (let [{:keys [precond-map effect-map reward]} this
                restrict (state-set/constrain ss (util/map-vals (fn [x] #{x}) precond-map))]
            (when-not (state-set/empty? restrict)
              [(state/set-vars ss (util/map-vals (fn [x] #{x}) effect-map)) reward])))]    
    {:optimistic-set-and-reward- exact
     :pessimistic-set-and-reward- exact}))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Automatic conversions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Default implementations for use with extend, for types that implement one protocol
; and not the other.

(defn explode-implicit-pair [[implicit-set reward]]
  (into {} (for [s (state-set/explicit-map implicit-set)])))

(def explicit-from-implicit
  {:optimistic-map- (fn implicit-optimistic-map [a s] )})




