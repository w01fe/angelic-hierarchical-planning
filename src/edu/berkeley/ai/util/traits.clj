(ns edu.berkeley.ai.util.traits
  (:require [edu.berkeley.ai.util :as util]))


(defn- parse-protocols-and-method-pairs [args]
  (when (seq args)
    (let [[proto & rest] args
          [methods more] (split-with coll? rest)]
      (println proto)
      (assert (symbol? proto))
      (cons [proto methods]
            (parse-protocols-and-method-pairs more)))))

(defn- parse-protocols-and-methods [args]
  (let [pairs (parse-protocols-and-method-pairs args)]
    (assert (apply distinct? (cons nil (map first pairs))))
    (into {} pairs)))

(defn- parse-bindings [b]
  (let [pairs (map vec (partition-all 2 b))]
    (assert (apply distinct? (cons nil (map first pairs))))
    (into {} pairs)))

(defmacro deftrait [name child-traits state-bindings & protocols-and-methods]
  `(def ~name
        '[~(set child-traits) ~(parse-bindings state-bindings) ~(parse-protocols-and-methods protocols-and-methods)]))

;(defmacro defrecord-trait [name fields ])

(defn- merge-traits [traits]
  (apply map apply
         [clojure.set/union util/merge-disjoint util/merge-disjoint]
         traits))

(defn- expand-traits
  "Expand out a set of traits into a single [binding-map impl-map]"
  [traits]
  (let [merged (merge-traits traits)]
    (rest (merge-traits [merged (expand-traits (first merged))]))))



(defmacro reify-traits [[& traits] specs]
  
  )