(ns angelic.sas.hm-heuristic
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.graphs :as graphs]
            [angelic.sas :as sas])
  (:import [java.util HashMap IdentityHashMap LinkedList]))

;; Obvious generalization of the hm heuristics to SAS+ problems.
;; Basic idea is to look for actio
;; First just implement h_max.

(set! *warn-on-reflection* true)

(defn h-max
  ([actions] (h-max actions [sas/goal-var-name sas/goal-true-val]))
  ([actions goal-pair]
     (let [a-map    (util/map-vals (partial map second)
                                   (group-by first (for [a actions, kv (:precond-map a)] [kv a])))
           init-a-counts (into {} (for [a actions] [a (count (:precond-map a))]))]
       (fn [state]
          (let [a-counts (IdentityHashMap. ^java.util.Map init-a-counts)
                closed   (HashMap.)]
            (loop [rew 0 open (LinkedList. (seq state)) next-open (LinkedList.)]
              (if (empty? open)
                (if (empty? next-open)
                  Double/NEGATIVE_INFINITY
                  (recur (dec rew) next-open open))
                (let [f (.remove open)]
                  (if (= f goal-pair)
                    rew
                    (do
                      (doseq [a (a-map f)]
                        (let [oc (.get a-counts a)
                              nc (dec oc)]
                          (.put a-counts a nc)
                          (when (= nc 0)
                            (doseq [ep (:effect-map a)]
                              (when-not (.containsKey closed ep)
                                (.put closed ep (+ rew (:reward a)))
                                (let [^LinkedList l (case (:reward a) 0 open -1 next-open)]
                                  (.offer l ep)))))))
                      (recur rew open next-open)))))))))))

(set! *warn-on-reflection* false)

; (let [e (make-random-infinite-taxi-sas2 5 5 2 5)] (print (h-max (:init e) (:actions e)) (second (uniform-cost-search e))) )