(ns angelic.search.incremental.implicit
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is]
            [angelic.search.incremental.hierarchical :as his])
  (:import  [java.util HashMap]))


;; For now, we'll assume "output trees" -- makes many things simpler.
;; Two options:
;; include ancestor reward in output-set reward
;; This preserves consistency across the board.  Seems like only sane option.
;; But then, have to keep parent links, be willing to refine parent through node.
;;  OR, have blocked-to-reduction.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Status ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 
(defn status-val [s]
  (case s
        :live    0
        :blocked 1
        :solved  2))

(defrecord Status [max-reward status])

(def +worst-status+ (Status. is/neg-inf :live))
(def +best-status+  (Status. is/pos-inf :solved))

(defn better-status? [s1 s2]
  (or (> (:max-reward s1)
         (:max-reward s2))
      (and (= (:max-reward s1)
              (:max-reward s2))
           (> (status-val (:status s1))
              (status-val (:status s2))))))

(defn- max-compare [cf arg1 & args]
  (if-let [[f & r] (seq args)]
    (recur cf (if (cf f arg1) f arg1) r)
    arg1))

(defn max-status [& stats] (apply max-compare better-status? (cons +worst-status+ stats) ))
(defn min-status [& stats] (apply max-compare (complement better-status?) (cons +best-status+ stats)))

(def zero-status (Status. 0 :solved))
(defn add-statuses [s1 s2]
  (Status. (+ (:max-reward s1)
              (:max-reward s2))
           (min-key status-val (:status s1) (:status s2))))

(defn refinable-status? [stat min-reward]
  (and (= (:status stat) :live)
       (>= (:max-reward stat) min-reward)))

(defn next-min-reward [stat min-reward]
  (min min-reward (:max-reward stat)))


(defn assert-unrefinable [status min-reward]
  (assert (not (refinable-status? status min-reward)))
  status)


(defmacro unrefinable-status-or [stat min-reward form]
  `(let [stat# ~stat]
     (if (refinable-status? stat# ~min-reward)
       ~form
       stat#)))

(defn max-thing-and-status [status-fn & things]
  (if (empty? things)
    [nil +worst-status+]
    (loop [best-thing (first things)
           best-status (status-fn (first things))
           more-things (rest things)]
      (if-let [[next-thing & even-more-things] (seq more-things)]
        (let [next-status (status-fn next-thing)]
          (if (better-status? next-status best-status)
            (recur next-thing next-status even-more-things)
            (recur best-thing best-status even-more-things)))))))

(defn remove-id [elt s]
  (remove #(identical? elt %) s))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: Ideally, would use effect sets rather than outcome sets?  

;; TODO: make sure we are actually lazy about refinements.

;; TODO: optimize this to prevent wasteful loops.

;; TODO: think about loops.  In particular, loop safety.

;; TODO: think about final split.  It is probably *not* always optimal, depending on which ops you count.

(def #^HashMap *subproblem-cache* nil)


(defrecord Subproblem [input-set action ^HashMap output-set-cache])


(declare osp-status refine-osp! refine-plan)

;; TODO: put back status caching!
(defrecord OutputSetNode    [plans child-pointers])

(defn osn-best-plan-and-status [osn]
  (max-thing-and-status :status (:plans osn)))

(defn osn-best-child-and-status [osn excluded-child-set]
  (max-thing-and-status osp-status (remove excluded-child-set (:child-pointers osn))))

(defn osn-status [osn excluded-child-set]
  (max-status (second (osn-best-plan-and-status osn)) (second (osn-best-child-and-status osn excluded-child-set))))

;; TODO: must add tricky bit here about increasing child reward.
(defn merge-children [subproblem child-pointers plans-by-output-set]
;  ...
  )

(defn refined-osn [osn min-reward excluded-child-set subproblem output-set]
  (let [[best-plan  plan-status]  (osn-best-plan-and-status osn)
        [best-child child-status] (osn-best-child-and-status osn excluded-child-set)
        best-status (max-status plan-status child-status)]
    (if (not (refinable-status? best-status min-reward))
      osn
      (if (better-status? child-status plan-status)
        (do (refine-osp! best-child (next-min-reward plan-status min-reward))
            (recur osn min-reward excluded-child-set subproblem output-set))
        (let [{:keys [plans child-pointers]} osn
              new-plans   (group-by :output-set (refine-plan best-plan (next-min-reward child-status min-reward)))
              other-plans (remove-id best-plan plans)]
          (recur (OutputSetNode.
                  (concat (new-plans output-set) other-plans)
                  (merge-children subproblem child-pointers (dissoc new-plans output-set)))
                 min-reward excluded-child-set subproblem output-set))))))


(defrecord OutputSetPointer [subproblem output-set node-atom alt-status])

(defn osp-status [osp exluded-child-set]
  (min-status (:alt-status osp) (osn-status @(:node-atom osp))))

(defn refine-osp! "Refine and return new status (blocked, solved, or worse than min-reward.)"
  ([osp min-reward] (refine-osp! osp min-reward #{}))
  ([osp min-reward excluded-child-set]
     (when (refinable-status? (:alt-status osp) min-reward)
       (assert-unrefinable
        (osn-status (swap! (:node-atom osp) refined-osn min-reward excluded-child-set (:subproblem osp) (:output-set osp))
                    excluded-child-set)
        min-reward))))





(declare make-initial-plan)

(defn make-initial-output-set-node [init-set action opt-reward]
  (OutputSetNode.
   (lazy-seq (for [[_ ref] (angelic/immediate-refinements-set)] (make-initial-plan init-set ref)))
   (Status. opt-reward :live)
   +worst-status+
   nil))


(defn get-subproblem-root-pointer [input-set action]
  (let [context (env/precondition-context action input-set)]
    (util/cache-with *subproblem-cache* [(state/extract-context input-set context) (env/action-name action)]
      (let [logged-input (state/get-logger input-set context)
            subproblem   (Subproblem. logged-input action (HashMap.))
            [opt rew]    (angelic/optimistic-set-and-reward action logged-input)
            init-node    (make-initial-output-set-node logged-input action rew)
            init-pointer (OutputSetPointer. subproblem opt (atom init-node) (Status. rew :live))]
        (.put ^HashMap (:output-set-cache subproblem) opt init-pointer)
        init-pointer))))



(defrecord PlanNode [sub-output-set-pointer excluded-child-set output-set-in-context status])
(defrecord Plan     [plan-nodes output-set status])

;; empty plan?

(defn make-initial-plan [init-set act-seq]
  (loop [status            zero-status
         last-output-set   init-set
         remaining-actions act-seq
         nodes             []]
    (if-let [[first-action & next-remaining-actions] (seq remaining-actions)]
      (let [root-ptr (get-subproblem-root-pointer last-output-set first-action)
            next-output-set (state/transfer-effects last-output-set (:output-set root-ptr))
            action-status (osp-status root-ptr)]
        (recur (add-statuses status action-status)
               next-output-set
               next-remaining-actions
               (conj nodes (PlanNode. root-ptr #{} next-output-set action-status))))

      (Plan. nodes last-output-set status))))






