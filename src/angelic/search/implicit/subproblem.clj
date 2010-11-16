(ns angelic.search.implicit.subproblem
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries])
  (:import  [java.util HashMap]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For now, go with simple "complete eval" formulation.
;; Will have "atomic" and "seq" subproblems -- separate impls..

;; unclear if we need refined?
;; blocked/solved should be autohandled by summarizer? 
(defprotocol Subproblem
  (subproblem-name [s])
  (input-set       [s])
  (output-set      [s])
  (expand!         [s])
  (child-keys      [s])
  (get-child       [s child-key])
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))

(defn refine-input [s maybe-refined-input-set]
  (if (= (input-set s) maybe-refined-input-set)
    s
    (refine-input- s maybe-refined-input-set)))

(traits/deftrait simple-subproblem [name input-set output-set delayed-child-map refine-input-fn] [] []
  Subproblem
   (subproblem-name [s] name)
   (input-set       [s] input-set)
   (output-set      [s] output-set)
   (expand!         [s]
     (summaries/expand! s (vals (force delayed-child-map))))
   (child-keys      [s]
     (assert (summaries/expanded? s))
     (keys (force delayed-child-map)))
   (get-child       [s child-key]
     (assert (summaries/expanded? s))
     (util/safe-get (force delayed-child-map) child-key))
   (refine-input-   [s refined-input-set] (refine-input-fn refined-input-set)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At least two ways we can do it -- keeping set of leaves, or following sum structure.
;; Do the latter for now.

(defn- remove-solution-noops [[a r]] [(remove #{[:noop]} a) r])

(defn solve [root-subproblem]
  (summary/solve
   #(summaries/verified-summary root-subproblem summary/+worst-simple-summary+)
   expand!
   #(let [n (-> % subproblem-name first)] (when-not (= n [:noop]) n))))
