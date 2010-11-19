(ns angelic.sas.hm-heuristic
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.graphs :as graphs]
            [angelic.sas :as sas])
  (:import [java.util IdentityHashMap LinkedList]))

;; Obvious generalization of the hm heuristics to SAS+ problems.
;; Basic idea is to look for actio
;; First just implement h_max.

(defn h-max [state actions]
  (let [a-map    (util/map-vals second
                  (group-by first (for [a actions, kv (:precond-map a)] [kv a])))
        a-counts (IdentityHashMap.
                  (into {} (for [a actions] [a (count (:precond-map a))])))
        closed   (HashMap.)
        goal-pair [sas/goal-var-name sas/goal-var-true]]
    (loop [rew 0 open (LinkedList. (seq init)) next-open (LinkedList.)]
      (if (empty? open)
        (if (empty? next-open)
          Double/NEGATIVE_INFINITY
          (recur (dec rew) next-open open))
        (let [f (.remove open)]
          (if (= f goal-pair)
            rew
            (doseq [a (a-map f)]
              (let [oc (.get a-counts a)
                    nc (dec oc)]
                (.put a-counts a nc)
                (when (= nc 0)
                  (doseq [ep (:effect-map a)]
                    (when-not (.contains closed ep)
                      (.put closed ep rew)
                      (.offer ^LinkedList (case (:reward a) 0 open -1 next-open) a))))))))))))


