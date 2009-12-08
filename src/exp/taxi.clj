(ns exp.taxi
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [hierarchy :as hierarchy]]
            ))

(defn make-left   [s]
  (let [cx     (env/get-var s '[atx])]
    (when (> cx 1) 
      (env/FactoredPrimitive ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn make-right  [s]
  (let [width  (env/get-var s '[width])
        cx     (env/get-var s '[atx])]
    (when (< cx width)  
      (env/FactoredPrimitive ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn make-down  [s]
  (let [cy     (env/get-var s '[aty])]
    (when (> cy 1)
      (env/FactoredPrimitive ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn make-up    [s]
  (let [height (env/get-var s '[height])
        cy     (env/get-var s '[aty])]
    (when (< cy height)
      (env/FactoredPrimitive ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn make-pickup  [s pass]
  (env/FactoredPrimitive 
       ['pickup pass] 
       {['atx] (env/get-var s ['srcx pass]) 
        ['aty] (env/get-var s ['srcy pass]) 
        ['pass-served? pass] false 
        ['in-taxi] nil}
       {['in-taxi] pass}
       -1))

(defn make-dropoff 
  ([s] (make-dropoff s (env/get-var s '[in-taxi])))
  ([s pass]
     (when pass 
       (let [dx (env/get-var s ['dstx pass])
             dy (env/get-var s ['dsty pass])]
         (env/FactoredPrimitive 
          ['dropoff pass] 
          {['atx] dx '[aty] dy '[in-taxi] pass}
          {'[in-taxi] nil ['pass-served? pass] true}
          -1)))))

(deftype TaxiEnv [width height passengers] :as this
 env/Env
  (initial-state []
    (into {['atx] 1 ['aty] 1 ['in-taxi] nil 
           ['width] width ['height] height}
        (apply concat
          (for [[name [sx sy] [dx dy]] passengers]
            [[['srcx name] sx] [['srcy name] sy]
             [['dstx name] dx] [['dsty name] dy]
             [['pass-served? name] false]]))))
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




; (use '[exp env taxi search hierarchy])
; (uniform-cost-search (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]])) 

(deftype NavHLA [env dx dy] :as this
  env/Action                (action-name [] ['nav dx dy])
  env/ContextualAction      (precondition-context [] [['atx] ['aty]])
  hierarchy/HighLevelAction (immediate-refinements [ s]
                             (if (and (= dx (env/get-var s ['atx])) 
                                      (= dy (env/get-var s ['aty])))
                               [[]]
                               (for [af [make-left make-right make-up make-down]
                                     :let [a (af s)]
                                     :when a]
                                 [a this]))))

(deftype ServeHLA [env pass] 
  env/Action                (action-name [] ['serve pass])
  env/ContextualAction      (precondition-context [] [['atx] ['aty] ['in-taxi] 
                                                      ['pass-served? pass]])
  hierarchy/HighLevelAction (immediate-refinements [s]
                             (let [[sx sy dx dy] 
                                   (map #(env/get-var s [% pass]) '[srcx srcy dstx dsty])
                                   pu (make-pickup  s pass)
                                   pd (make-dropoff s pass)]
                               (util/assert-is (and pu pd))
                               [[(NavHLA env sx sy) pu (NavHLA env dx dy) pd]])))

(deftype TaxiTLA [env]      :as this
  env/Action                (action-name [] ['top])
  env/ContextualAction      (precondition-context [] (keys (env/initial-state env)))
  hierarchy/HighLevelAction (immediate-refinements [s]
                              (let [remaining-passengers
                                    (for [[pass] (:passengers env)
                                          :when (not (env/get-var s ['pass-served? pass]))]
                                      pass)]
                                (if (empty? remaining-passengers)
                                    [[]]
                                  (for [pass remaining-passengers]
                                    [(ServeHLA env pass) this])))))



(defn simple-taxi-hierarchy [#^TaxiEnv env]
  (hierarchy/SimpleHierarchicalEnv
   env
   [(TaxiTLA env)
    (env/make-finish-action env)]))

; (uniform-cost-search (ShopHTNEnv (simple-taxi-hierarchy (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]]))))