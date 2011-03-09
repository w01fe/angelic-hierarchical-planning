(ns angelic.search.explicit.flat
  (:require [angelic.util :as util]
            [angelic.env :as env] 
            [angelic.search.explicit.core :as is])
  (:import  [java.util HashMap]))


(defn make-forward-search 
  "Make a forward search that stops at goals."
  [env] 
  (let [actions-fn (env/actions-fn env), goal-fn (env/goal-fn env), is (env/initial-state env)]
    (is/make-flat-incremental-dijkstra 
     (is/make-simple-node is 0 (goal-fn is) [])
     #(let [state (is/node-name %)]
       (for [a (actions-fn state)
             :when (env/applicable? a state)
             :let  [[ss r] (env/successor a state)]]
         (is/make-simple-node ss (+ (is/max-reward %) r) (goal-fn ss) (conj (:data %) a)))))))

(defn uniform-cost-search [env] 
  (when-let [g (is/first-goal-node (make-forward-search env))]
    [(:data g) (is/max-reward g)]))
