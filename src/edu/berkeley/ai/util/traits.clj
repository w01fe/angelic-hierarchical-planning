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
;  (println traits)
  (apply map (fn [f & args] (apply f args))
         [clojure.set/union util/merge-disjoint util/merge-disjoint]
         traits))

(defn- expand-traits
  "Expand out a set of traits into a single [binding-map impl-map]"
  [traits]
  (if (seq traits)  
    (let [merged (merge-traits traits)]
      (rest (merge-traits [merged (expand-traits (first merged))])))
      [#{} {} {}]))


(defn- render-trait-methods-inline [trait-map]
  (apply concat (map (partial apply cons) trait-map)))


(defmacro reify-traits [[& traits] & specs]
  (println traits)
  (let [[trait-bindings trait-methods] (expand-traits (map eval traits))]
    `(let ~(vec (apply concat trait-bindings))
       (reify
        ~@(render-trait-methods-inline trait-methods)
        ~@specs))))


(comment         

 (defprotocol P2
   (p21 [x y])
   (p22 [x]))


 (defprotocol P1
   (p11 [x y]))

 (defprotocol P0)

 (deftrait +foo+ [] [x 2 y (atom nil)] P2 (p21 [x y] (+ x y)) (p22 [x] (inc x)) P0)

 (deftrait +bar+ [] [z (atom nil) a 4] P1 (p11 [x y] (- x y))))

