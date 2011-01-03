(ns angelic.search.implicit.subproblem-eval
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]            
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]))

;; Subproblems where we allow explicit evaluation, along with lazy child generation.
;; Putting the focus on evaluation gives us finer granularity,
;; allowing full utilizatino of subsumption, plus is more natural in a decomposed
;; setting where we also have to "evaluate" existing actions in new contexts.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A subproblem should also implement Summarizable and Refinable implementations.
;; The non-viable (pre-refinement) subproblem is always represented as nil.

;; Here, get-child and refine-input always return subproblems,
;; but output-set can return "nil"
;; get-child and refine-input are allow to return nil 

(defprotocol Subproblem
  (subproblem-name [s])
  (input-set       [s])
  (evaluate!       [s] "Evaluating will eventually produce output-set, but may require multiple steps.
                        Returns (non-empty) output-set when evaluation is finished, or nil if not/dead.
                        Does not refresh summary.")
  (evaluated?      [s] "Is an output-set ready?")
  (output-set      [s])
  (child-keys      [s])
  (get-child       [s child-key]))


;; also want part of evaluate here.
;; return a new reward, status OR output-set, and child-map iff output set:
(defprotocol Refinable
  (evaluate-       [s] "return [output-set delay-child-map] output-pair or nil, if
                        dead / more eval needed.  Update summary to match as needed.")
  (refine-input-   [s refined-input-set] "must be a strict subset of input-set."))

(defn refine-input [s maybe-refined-input-set]
  (if (= (input-set s) maybe-refined-input-set)
    s
    (when-let [refined (refine-input- s maybe-refined-input-set)]
      (summaries/connect! refined s true)
      refined)))

;; Output-pair is [output-set init-summarizable]
(traits/deftrait simple-subproblem [name input-set summarizable]
  [output-pair-atom (atom :wait)
   ensure-expanded  (fn [s] (when-not (summaries/expanded? s)
                              (summaries/expand! s (vals (force (second @output-pair-atom))))))]
  [(summaries/simple-or-summarizable summarizable)]
  Subproblem
   (subproblem-name [s] name)
   (input-set       [s] input-set)
   (evaluate!       [s]
     (assert (not (evaluated? s)))
     (util/prog1
      (when-let [output-pair (evaluate- s)]
        (reset! output-pair-atom output-pair)
        (first output-pair))))
   
   (evaluated?      [s] (not (= :wait @output-pair-atom)))
   (output-set      [s] (first @output-pair-atom))
   (child-keys      [s] (ensure-expanded s) (keys (force (second @output-pair-atom))))
   (get-child       [s child-key] (ensure-expanded s) (util/safe-get (force (second @output-pair-atom)) child-key)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At least two ways we can do it -- keeping set of leaves, or following sum structure.
;; Do the latter for now.

(defn- remove-solution-noops [[a r]] [(remove #{[:noop]} a) r])

(defn solve [root-subproblem]
  (summary/solve
   #(summaries/extract-verified-unexpanded-leaf root-subproblem)
   #(let [src (summary/source %)]
      (if (evaluated? src)
        (do (assert (not (summaries/expanded? src))) (child-keys src))
        (evaluate! src)))
   #(let [n (summaries/label %)] (when-not (= (first n) :noop) n))))

(comment
 (defn pseudo-solve [root-sp]
   (summaries/pseudo-solve root-sp summary/+worst-simple-summary+ (complement summaries/expanded?)
                           #(if (evaluated? %) (do (assert (not (summaries/expanded? %))) (child-keys %)) (evaluate! %)))))
