(ns angelic.search.incremental.implicit-fah-astar
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [clojure.contrib.core :as ccc]
            [angelic.env :as env]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is])
  (:import  [java.util HashMap]))


;; Factored abstract lookahead trees
;; I.e., the real DASH-A* should be reached by adding DS to this.
;; Much copied from previous ipmlicit-dash-a*.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Misc. Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Summary is the information passed upwards about a partial plan.
;; For now, it consists of an (admissible) upper-bound on reward,
;; a status enum -- :live, :blocked, or :solved,
;; and if solved, an optimal solution.

(defprotocol Summary
  (max-reward       [s] "Admissible reward bound")
  (live?            [s] "Can this be further refined?")
  (optimal-solution [s] "Nil or optimal solution"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Definition ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 
(defn status-val [s]
  (case s
        :live    0
        :blocked 1
        :solved  2))


(defrecord SimpleSummary [max-rew status opt-sol]
  Summary
  (max-reward       [s] max-rew)
  (live?            [s] (= status :live))
  (optimal-solution [s] (when (= status :solved) (assert opt-sol) opt-sol)))

(defn make-live-summary [max-reward plan] (SimpleSummary. max-reward :live plan))
(defn make-blocked-summary [max-reward plan] (SimpleSummary. max-reward :blocked plan))
(defn make-solved-summary [max-reward opt-sol] (SimpleSummary. max-reward :solved opt-sol))

(defn blocked? [summary]
  (and (not (live? summary))
       (not (optimal-solution summary))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Common Ops ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def +worst-summary+ (make-blocked-summary is/neg-inf []))
(def +best-summary+  (make-live-summary is/pos-inf [])) ;; don't be too optimistic

(defn better-summary? [s1 s2]
  (or (> (max-reward s1)
         (max-reward s2))
      (and (= (max-reward s1)
              (max-reward s2))
           (> (status-val (:status s1))
              (status-val (:status s2))))))

(defn- max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

(defn max-summary [& stats] (apply max-compare better-summary? (cons +worst-summary+ stats) ))
;(defn min-summary [& stats] (apply max-compare (complement better-summary?) (cons +best-summary+ stats)))

(defn bound-summary [summary max-rew]
  (when (optimal-solution summary) (util/assert-is (<= (max-reward summary) max-rew)))
  (SimpleSummary. (min max-rew (:max-rew summary)) (:status summary) (:opt-sol summary)))

(defn next-min-reward [stat min-reward] (max min-reward (max-reward stat)))

(def zero-summary (SimpleSummary. 0 :solved []))
(defn add-summaries [s1 s2]
  (SimpleSummary. (+ (max-reward s1)
              (max-reward s2))
           (min-key status-val (:status s1) (:status s2))
           #_(when (and (= (:status s1) :solved) (= (:status s2) :solved)))
           (concat (:opt-sol s1) (:opt-sol s2))))


(defn viable-summary? [summary]
  (> (max-reward summary) is/neg-inf))

(defn refinable-summary? [stat min-reward]
  (and (= (:status stat) :live)
       (>= (max-reward stat) min-reward)))

(defn summary-solution [stat]
  (when (= (:status stat) :solved)
    (:opt-sol stat)))



(defn extract-best-and-summaries
  "Return [best-item best-summary rest-items rest-summary]"
  [summary-fn things]
  (assert (seq things))
  (loop [best-thing   (first things)
         best-summary (summary-fn (first things))
         rest-things  []
         rest-summary  +worst-summary+
         more-things  (rest things)]
      (if-let [[next-thing & even-more-things] (seq more-things)]
        (let [next-summary (summary-fn next-thing)]
          (if (better-summary? next-summary best-summary)
            (recur next-thing next-summary
                   (conj rest-things best-thing) best-summary even-more-things)
            (recur best-thing best-summary
                   (conj rest-things next-thing) (max-summary next-summary rest-summary) even-more-things)))
        [best-thing best-summary rest-things rest-summary])))

(defn summary-str [s] (str "Summary:" (max-reward s) (:status s) #_ (vec (:opt-sol s))))
(defmethod print-method SimpleSummary [s o] (print-method (summary-str s) o))

(defmacro assert-valid-summary-change
  ([old-summary new-summary] ( assert-valid-summary-change old-summary new-summary ""))
  ([old-summary new-summary msg]
     `(do (util/assert-is (<= (max-reward ~new-summary) (max-reward ~old-summary)) "%s" [~old-summary ~new-summary ~msg])
        (when-not (live? ~old-summary) (assert (= ~old-summary ~new-summary))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Refinements all have at least one action, constraints are new primitives.  

(defrecord ActionInstance
  [parent-ri
   super-ai
   prev-aio
   actions ; this and following in refinement.
   output-atom ])

(defrecord ActionInstanceOutput
  [prev-ai
   output-set
   step-reward
   refinements
   next-ai-atom])

(def +worst-aio+ (ActionInstanceOutput. nil state-set/empty-lfss is/neg-inf nil nil))

(defrecord RefinementInstance
  [parent-ai
   super-ri
   first-ai-atom])

(defn make-refinement-instance [parent-ai actions]
  (let [ri (RefinementInstance. parent-ai nil (atom nil))]
    (reset! (:first-ai-atom ri)
            (ActionInstance. ri nil (:prev-aio parent-ai) actions (atom nil)))
    ri))


(defn make-refinement-instance-child [parent-ai sup-ri]
  (let [ri (RefinementInstance. parent-ai sup-ri (atom nil))
        sup-ai (-> sup-ri :first-ai-atom deref)]
    (reset! (:first-ai-atom ri)
            (ActionInstance. ri sup-ai (:prev-aio parent-ai) (:actions sup-ai) (atom nil)))
    ri))

(defn make-aio [ai]
  (let [{:keys [parent-ri super-ai prev-aio actions output-atom]} ai]
    (assert (nil? @output-atom))
    (let [input-set (:output-set prev-aio)
          [a & r]   actions
          prim?    (env/primitive? a)
          [opt rew] (angelic/optimistic-set-and-reward a input-set)]
      (if (or (not opt) (state-set/empty? opt) (= rew is/neg-inf))
        +worst-aio+
        (ActionInstanceOutput.
         ai opt rew
         (lazy-seq
          (let [super-refs (ccc/-?> super-ai :output-atom deref refinements)]
            (cond (and super-refs (not (= super-refs :blocked)))
                    (for [super-ri super-refs]
                      (make-refinement-instance-child ai super-ri))
                  (angelic/can-refine-from-set? a input-set)
                    (for [[constraint ref] (angelic/immediate-refinements-set a input-set)]
                      (make-refinement-instance
                       ai
                       (cons (env-util/make-factored-primitive [:noop] constraint {} 0) ref))
                  :else
                  :blocked))))
         (atom nil))))))

(defn extend-aio! [aio]
  (when-let [ai (:prev-ai aio)]
    (let [target-ai (util/find-first #(> (count (:actions %)) 1)
                                     (iterate #(-> % :parent-ri :parent-ai) ai))]
      (reset! (:next-ai-atom aio)
              (ActionInstance.
               (:parent-ri target-ai)
               (if (not (identical? ai target-ai))
                 target-ai
                 (ccc/-?> ai :super-ai output-atom deref next-ai-atom deref))
               aio
               (next (:actions target-ai))
               (atom nil))))))

(defn evaluate-ai! [ai]
  (let [aio (make-aio ai)]
    (reset! (:output-atom ai) aio)
    (extend-aio! aio)))

;; MAke a special finish that cannot be evaluated.
;; Now, can start with all unevaluated actions (ends of the line). Push reward back, up to parentAI, down to subs.
;; This leaves out pushing down refs.  Allows to "fill in" for unevaluated refs. That would be unnec. with superstructure?
;; Problem: how do we determine current best bound? 
;; Idea: costs go forward, down to refinements, only up when necessary. (i.e, unevaluated node).
;; Bound is only relevant if it includes at least one live thing???
;; But, we really want to do factored evaluation of costs.

;; Bound(AN) = min(Reward(AN), Bound(SupAN), max(Bound(RefinementNodes)))
;; Bound(RN) = min(PathSum(FirstAN))
;; PathSum(AN) = Bound(AN) + (no more ???)

;; Suppose we have OutputLattice on 