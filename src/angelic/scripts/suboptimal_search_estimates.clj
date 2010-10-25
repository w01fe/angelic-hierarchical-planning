(ns angelic.scripts.suboptimal-search-estimates
  (:require [clojure.contrib.math :as math])
  )

;; Suppose we want a w-optimal plan, AKA must raise bound on alternative plan above (b^d) / w

;; Heuristic estimate for action at 
;; abstraction level a is c * (1 - e * a/d), c is true cost (TLA has abstraction level d).  
;; Spse primitive branching factor is p.

;; To get primitive cost above b^d / w, need length l of primitive part s.t.
;; l + (b^d - l) * (1 - e) >= (b^d) / w
;; l >= (b^d) (1/w - (1-e)) / e
;; l >= (b^d) (1/w - (1-e)) / e

;; Cost is 1 + p + p^2 + ... + p^l = (1-p)^(l+1)/(1-p) = 
;; O(p^l)

;; To do it top-down, need to go to abstraction level a s.t.

;; b^d * (1 - e * a / d) >= b^d / w
;; e * a / d <= 1 - 1 / w 
;; a <= d * (1 - 1/w)/e
;; Cost is 1 + b + ... + b^(d - a) = O(b^(d-a))

(defn geometric-sum [a r n]
  (* a (/ (- 1 (math/expt r (inc n))) (- 1 r))))

(defn primitive-proportion
  "What proportion of a plan must be primitive to achieve weight w
   given heristic underestimates by epsilon?"
  [weight epsilon]
  (/ (- (/ 1 weight) (- 1 epsilon)) epsilon))

(defn primitive-cost
  "How much does it cost to raise bound above (1/w) of true,
   assuming unit action costs."
  [true-length branch-factor weight epsilon]
  (geometric-sum
   1
   branch-factor
   (int (+ 0.9999 (* (max 0 (min 1 (primitive-proportion weight epsilon))) true-length)))))

(defn abstraction-proportion
  "What abstraction level must we go to?"
  [weight epsilon]
  (/ (- 1 (/ 1 weight)) epsilon))

(defn angelic-cost
  [depth ref-branch-factor ref-length weight epsilon]
  (geometric-sum
   1
   (* ref-branch-factor ref-length)
   (- depth (int (* depth (min 1 (abstraction-proportion weight epsilon)))))))

(defn both-costs
  [ref-length depth ref-branch-factor prim-branch-factor weight epsilon]
  [(primitive-cost (math/expt ref-length depth) prim-branch-factor weight epsilon)
   (angelic-cost depth ref-branch-factor ref-length weight epsilon)])
