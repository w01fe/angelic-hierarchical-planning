(ns exp.taxi
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util Random]))

(defn make-left   [s]
  (let [cx     (env/get-var s '[atx])]
    (when (> cx 1) 
      (env/FactoredPrimitive ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn make-right  [s]
  (let [const (env/get-var s :const)
        width  (get const '[width])
        cx     (env/get-var s '[atx])]
    (when (< cx width)  
      (env/FactoredPrimitive ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn make-down  [s]
  (let [cy     (env/get-var s '[aty])]
    (when (> cy 1)
      (env/FactoredPrimitive ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn make-up    [s]
  (let [const (env/get-var s :const)
        height (get const '[height])
        cy     (env/get-var s '[aty])]
    (when (< cy height)
      (env/FactoredPrimitive ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn make-pickup  [s pass]
  (let [const (env/get-var s :const)]
    (env/FactoredPrimitive 
     ['pickup pass] 
     {['atx] (get const ['srcx pass]) 
      ['aty] (get const ['srcy pass]) 
      ['pass-served? pass] false 
      ['in-taxi] nil}
     {['in-taxi] pass}
     -1)))

(defn make-dropoff 
  ([s] (make-dropoff s (env/get-var s '[in-taxi])))
  ([s pass]
     (when pass 
       (let [const (env/get-var s :const)
             dx (get const ['dstx pass])
             dy (get const ['dsty pass])]
         (env/FactoredPrimitive 
          ['dropoff pass] 
          {['atx] dx '[aty] dy '[in-taxi] pass}
          {'[in-taxi] nil ['pass-served? pass] true}
          -1)))))


(deftype TaxiEnv [width height passengers] :as this
 env/Env
  (initial-state []
    (into {:const (into {['width] width ['height] height}
                      (apply concat
                       (for [[name [sx sy] [dx dy]] passengers]
                         [[['srcx name] sx] [['srcy name] sy]
                          [['dstx name] dx] [['dsty name] dy]])))
           ['atx] 1 ['aty] 1 ['in-taxi] nil}
          (for [[name [sx sy] [dx dy]] passengers]
            [['pass-served? name] false])))
  (actions-fn []
   (fn taxi-actions [s]
     (filter identity
       (concat (map #(% s) [make-left make-right make-up make-down make-dropoff])
               (for [[pass] passengers] (make-pickup s pass))))))
  (goal-fn [] 
    (let [goal-map (env/goal-map this)]
      #(when (env/state-matches-map? % goal-map)
         (env/solution-and-reward %))))
 env/FactoredEnv
  (goal-map [] (into {} (for [[pass] passengers] [['pass-served? pass] true]))))


;; TODO: think about a sort of concentration parameter for common positions.
(defn make-random-taxi-env 
  ([width height n-passengers] 
     (make-random-taxi-env width height n-passengers (rand-int 10000000)))
  ([width height n-passengers seed]
     (let [r (Random. seed)]
       (.nextDouble r) (.nextDouble r)
       (TaxiEnv width height
                (for [i (range n-passengers)]
                  [(symbol (str "pass" i))
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]])))))


; (use '[exp env taxi search hierarchy])
; (uniform-cost-search (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]])) 

(deftype NavHLA [env dx dy] :as this
  env/Action                (action-name [] ['nav dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['atx] ['aty]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (if (and (= dx (env/get-var s ['atx])) 
                                      (= dy (env/get-var s ['aty])))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)]
                                     :when a]
                                 [a this])))
                            (cycle-level- [s] 1))

(deftype ServeHLA [env pass] 
  env/Action                (action-name [] ['serve pass])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['atx] ['aty] ['in-taxi] 
                                                      ['pass-served? pass]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [const (env/get-var s :const)
                                   [sx sy dx dy] 
                                     (map #(get const [% pass]) '[srcx srcy dstx dsty])
                                   pu (make-pickup  s pass)
                                   pd (make-dropoff s pass)]
                               (util/assert-is (and pu pd))
                               [[(NavHLA env sx sy) pu (NavHLA env dx dy) pd]]))
                            (cycle-level- [s] nil))

(deftype TaxiTLA [env context]      :as this
  env/Action                (action-name [] ['top])
                            (primitive? [] false)  
  env/ContextualAction      (precondition-context [s] context)
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [remaining-passengers
                                    (for [[pass] (:passengers env)
                                          :when (not (env/get-var s ['pass-served? pass]))]
                                      pass)]
                                (if (empty? remaining-passengers)
                                    [[(env/make-finish-action env)]]
                                  (for [pass remaining-passengers]
                                    [(ServeHLA env pass) this]))))
                            (cycle-level- [s] nil))

(defn make-taxi-tla [env]
  (TaxiTLA env (keys (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy [#^TaxiEnv env]
  (hierarchy/SimpleHierarchicalEnv
   env
   [(make-taxi-tla env)]))


(defn simple-taxi-hierarchy-nsa [#^TaxiEnv env]
  (hierarchy/SimpleHierarchicalEnv
   env
   [(hierarchy/NSAHLA (make-taxi-tla env) (keys (dissoc (env/initial-state env) :const)))]))

; (uniform-cost-search (ShopHTNEnv (simple-taxi-hierarchy (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]]))))



;; Slightly fancier hierarchy that splits navigation.
(deftype NavHHLA [env dx] :as this
  env/Action                (action-name [] ['navh dx])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['atx]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (if (= dx (env/get-var s ['atx]))                                                                    [[]]
                                (for [af [make-left make-right]
                                     :let [a (af s)]
                                     :when a]
                                 [a this])))
                            (cycle-level- [s] 1))

(deftype NavVHLA [env dy] :as this
  env/Action                (action-name [] ['navv dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['aty]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (if (= dy (env/get-var s ['aty]))                                                                    [[]]
                                (for [af [make-up make-down]
                                     :let [a (af s)]
                                     :when a]
                                 [a this])))
                            (cycle-level- [s] 1))

(deftype Nav2HLA [env dx dy] :as this
  env/Action                (action-name [] ['nav dx dy])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['atx] ['aty]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             [[(NavHHLA env dx) (NavVHLA env dy)]])
                            (cycle-level- [s] nil))

(deftype Serve2HLA [env pass] 
  env/Action                (action-name [] ['serve pass])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] [['atx] ['aty] ['in-taxi] 
                                                      ['pass-served? pass]])
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [const (env/get-var s :const)
                                   [sx sy dx dy] 
                                     (map #(get const [% pass]) '[srcx srcy dstx dsty])
                                   pu (make-pickup  s pass)
                                   pd (make-dropoff s pass)]
                               (util/assert-is (and pu pd))
                               [[(Nav2HLA env sx sy) pu (Nav2HLA env dx dy) pd]]))
                            (cycle-level- [s] nil))

(deftype Taxi2TLA [env context]      :as this
  env/Action                (action-name [] ['top])
                            (primitive? [] false)  
  env/ContextualAction      (precondition-context [s] context)
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [remaining-passengers
                                    (for [[pass] (:passengers env)
                                          :when (not (env/get-var s ['pass-served? pass]))]
                                      pass)]
                                (if (empty? remaining-passengers)
                                    [[(env/make-finish-action env)]]
                                  (for [pass remaining-passengers]
                                    [(Serve2HLA env pass) this]))))
                            (cycle-level- [s] nil))

(defn make-taxi-tla2 [env]
  (Taxi2TLA env (keys (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy2 [#^TaxiEnv env]
  (hierarchy/SimpleHierarchicalEnv
   env
   [(make-taxi-tla2 env)]))

