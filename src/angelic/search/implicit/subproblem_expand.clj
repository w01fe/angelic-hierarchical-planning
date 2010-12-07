(ns angelic.search.implicit.subproblem-expand
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]))

;; A first version of implicit subproblems, where computation steps are expansions
;; (and evaluations are always eager).  
;; The problem with this is that we do a lot of evaluations per each expansion,
;; and potentially even moreso when in a decomposed framework.  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A subproblem should also implement Summarizable and Refinable implementations.
;; The non-viable (pre-refinement) subproblem is always represented as nil.

(defprotocol Refinable
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))

(defn refine-input [s maybe-refined-input-set]
  (if (= (input-set s) maybe-refined-input-set)
    s
    (when-let [refined (refine-input- s maybe-refined-input-set)]
      (summaries/connect! s refined true)
      refined)))

;; get-child and refine-input are allow to return nil 

(defprotocol Subproblem
  (subproblem-name [s])
  (input-set       [s])
  (output-set      [s] "Always non-empty.")
  (expand!         [s])
  (child-keys      [s])
  (get-child       [s child-key]))

(traits/deftrait simple-subproblem [name input-set output-set delayed-child-map] [] []
  Subproblem
   (subproblem-name [s] name)
   (input-set       [s] input-set)
   (output-set      [s] output-set)
   (expand!         [s]
     (summaries/expand! s (remove nil? (vals (force delayed-child-map)))))
   (child-keys      [s]
     (assert (summaries/expanded? s))
     (keys (force delayed-child-map)))
   (get-child       [s child-key]
     (assert (summaries/expanded? s))
     (util/safe-get (force delayed-child-map) child-key)))



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
   #(let [n (-> % subproblem-name first)] (when-not (= (first n) :noop) n))))
