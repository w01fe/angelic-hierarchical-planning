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

(defn merge-traits [& traits]
  (let [bindings  (vec (apply concat (map first traits)))]
    (assert (apply distinct? (take-nth 2 bindings)))
    [bindings
     (reduce util/merge-disjoint {} (map second traits))]))

(defn parse-trait-form [traits]
  (vec (map #(if (list? %) % (list %)) traits)))

;; Internal rep. of a trait is a fn from args to [binding-seq impl-map]
;; TODO: forn ow, args may be multiple evaluated?
(defmacro deftrait [name args state-bindings child-traits & protocols-and-methods]
  `(defn ~name ~args
     (apply merge-traits
      [(concat (interleave '~args ~args) '~state-bindings)
        '~(parse-protocols-and-methods protocols-and-methods)]
      ~(parse-trait-form child-traits))))

(defn- render-trait-methods-inline [trait-map]
  (apply concat (map (partial apply cons) trait-map)))

(defmacro reify-traits [[& traits] & specs]
  (println (eval (parse-trait-form traits)))
  (let [[trait-bindings trait-methods] (apply merge-traits (eval (parse-trait-form traits)))]
    (println trait-bindings)
    `(let ~trait-bindings
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

 (deftrait +foo+ [x] [y (atom x)] [] P2 (p21 [x z] (+ z @y)) (p22 [x] (swap! y inc)) P0)

 (deftrait +bar+ [w] [z (inc w)] [(+foo+ (* w 2))] P1 (p11 [x y] (- y w))))

