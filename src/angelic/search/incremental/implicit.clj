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
;; blocked-to-reduction might be nice, since it will prevent every osn from being
;; contaminated by a single bad parent.  If at low level many things leapfrog over top,
;; every refinement will be severely magnified.
;; Except: this is TOTALLY UNAVOIDABLE without some sort of out-of-band communication.
;; and how would this comm work, exactly?
;; Whenever refinement is done, must notify somehow about excluded children
;; whose reward has increased since last refinement done
;; (although their reward may currently be lower, having passed it on further, if caching.)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Misc. Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn remove-id [elt s]
  (remove #(identical? elt %) s))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Status ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Definition ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; status is: :blocked, :solved, or :live
;; blocked is "better" than live, since it is contagious over live w.r.t. max. 
(defn status-val [s]
  (case s
        :live    0
        :blocked 1
        :solved  2))

(defrecord Status [max-reward status])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Common Ops ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

(defn max-thing-status-and-next [status-fn & things]
  (if (empty? things)
    [nil +worst-status+ +worst-status+]
    (loop [best-thing (first things)
           best-status (status-fn (first things))
           next-best-status +worst-status+
           more-things (rest things)]
      (if-let [[next-thing & even-more-things] (seq more-things)]
        (let [next-status (status-fn next-thing)]
          (if (better-status? next-status best-status)
            (recur next-thing next-status best-status even-more-things)
            (recur best-thing best-status (max-status next-status next-best-status) even-more-things)))))))

(defn one-operation-on-best [status-fn1 s1 op1 status-fn2 s2 op2 min-reward default]
  (let [[best1 status1 ns1] (max-thing-status-and-next status-fn1 s1)
        [best2 status2 ns2] (max-thing-status-and-next status-fn2 s2)
        best-status     (max-status status1 status2)]
    (if (not (refinable-status? best-status min-reward))
      default
      (if (better-status? status2 status1)
        (op2 best2 (next-min-reward (max-status ns2 status1) min-reward))
        (op1 best1 (next-min-reward (max-status ns1 status2) min-reward))))))

(defn operate-on-best [status-fn1 seq-fn1 op1 status-fn2 seq-fn2 op2 init next-fn min-reward]
  (last
   (util/iterate-while
    #(when-let [x (one-operation-on-best status-fn1 (seq-fn1 %) op1 status-fn2 (seq-fn2 %) op2 min-reward nil)]
       (next-fn x))
    init)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Ideally, would use effect sets rather than outcome sets?  
;; TODO: make sure we are actually lazy about refinements.
;; TODO: add value caching, for plan seqs, children, ancestors.
;; TODO: think about loops.  In particular, loop safety.
;; TODO: think about final split.  It is probably *not* always optimal, depending on which ops you count.

(def #^HashMap *subproblem-cache* nil)

;; output-set-cache currently not used. 
(defrecord Subproblem [input-set input-context action ^HashMap output-set-cache])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Trees ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OSP trees contain pointers, which are permenant things representing a SAS combo,
;; and nodes, which contain the current state of the search (including links to child pointers).

;; TODO: put back status caching!

; Dependencies on plans
(declare make-initial-plan expand-plan)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dependencies on pointers
(declare osp-status refine-osp! add-plans-osp! make-child-osp )


(defrecord OutputSetNode    [plans child-pointers])

(defn make-initial-output-set-node [init-set action opt-reward]
  (OutputSetNode.
   (lazy-seq (for [[constraint ref] (angelic/immediate-refinements-set)] (make-initial-plan init-set constraint ref)))
   (Status. opt-reward :live)
   +worst-status+
   nil))



(defn osn-plan-status [osn] (apply max-status (map :status (:plans osn))))
(defn osn-child-status [osn ecs] (apply max-status (map osp-status (remove ecs (:child-pointers osn)))))
(defn osn-status [osn ecs] (max-status (osn-plan-status osn) (osn-child-status osn ecs)))

;; osn/osp
(defn merge-children
  "Merge a map from output sets to plans with the current children of osn."
  [parent-osp osn plans-by-output-set]
  (concat
   (:child-pointers osn)
   (for [[os plans] (reduce (fn [pos c] (add-plans-osp! c pos)) plans-by-output-set (:child-pointers osn))]
     (make-child-osp parent-osp os plans))))


(defn refine-osn-plan
  "Refine a single plan stored at this osn."
  [parent-osp osn best-plan min-reward subproblem output-set]
  (let [{:keys [plans child-pointers]} osn
        new-plans   (group-by :output-set (expand-plan best-plan min-reward))
        other-plans (remove-id best-plan plans)]
    (OutputSetNode.
     (concat (new-plans output-set) other-plans)
     (merge-children parent-osp osn (dissoc new-plans output-set)))))

(defn refined-osn
  "Repeatedly refine plans stored at this osn or below."
  [osn min-reward excluded-child-set subproblem output-set]
  (operate-on-best
   :status    :plans                     #(refine-osn-plan osn %1 %2 subproblem output-set)
   osp-status #(remove excluded-child-set (:child-pointers %)) #(do (refine-osp! %1 %2) %1)
   osn identity min-reward))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Pointers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord OutputSetPointer [subproblem parent-pointer output-set node-atom alt-status])

(defn make-child-osp [parent-osp output-set plans]
  (OutputSetPointer. (:subproblem parent-osp) parent-osp output-set (OutputSetNode. plans nil) +best-status+))

(defn osp-ancestors [osp]
  (when-let [p (:parent-pointer osp)]
    (cons p (lazy-seq (osp-ancestors osp)))))

(defn osp-plan-status [osp] (osn-plan-status @(:node-atom osp)))

(defn osp-status [osp excluded-child-set]
  (min-status (:alt-status osp)
              (apply max-status
                     (osn-status @(:node-atom osp) excluded-child-set)
                     (map osn-plan-status (osp-ancestors osp)))))

(defn refine-osp!
  "Repeatedly refine an ancestor or descendent of this node."
  [osp min-reward excluded-child-set]
  (operate-on-best
   osp-plan-status osp-ancestors refine-osp!
   osp-status [osp] #(swap! (:node-atom osp) refined-osn %2 excluded-child-set (:subproblem osp) (:output-set osp))))

(defn add-plans-osp!
  "Add plans from map and return map with them removed"
  [osp plans-by-output-set]
  (if-let [plans (get plans-by-output-set (:output-set osp))]
    (do (swap! (:node-atom osp) update-in [:plans] concat plans)
        (dissoc plans-by-output-set (:output-set osp)))
    plans-by-output-set))

(defn split-osp
  "Return new-child-osps.  Currently splits children < min-reward when parent >= min-reward."
  [osp min-reward excluded-child-set]
  (when (> (:max-reward (osp-plan-status osp)) min-reward)
    (filter #(<= (:max-reward (osp-status %)))
            (remove excluded-child-set
                    (:child-pointers @(:node-atom osp))))))



;;;;;;;;;;;;;;;;;;;;;;; Making and Splitting Subproblems ;;;;;;;;;;;;;;;;;;;;;;;

(defn get-subproblem-root-pointer [input-set action reward-bound-fn]
  (let [context (env/precondition-context action input-set)
        state-context (state/extract-context input-set context)]
    (util/cache-with *subproblem-cache* [state-context (env/action-name action)]
      (let [logged-input (state/get-logger input-set context)
            subproblem   (Subproblem. logged-input state-context action (HashMap.))
            [opt rew]    (angelic/optimistic-set-and-reward action logged-input)
            rew          (min rew (reward-bound-fn))
            init-node    (make-initial-output-set-node logged-input action rew)
            init-pointer (OutputSetPointer. subproblem nil opt (atom init-node) (Status. rew :blocked))]
        (.put ^HashMap (:output-set-cache subproblem) opt init-pointer)
        init-pointer))))

(defn refine-osp-input [osp new-input-set]
  (let [root-osp         (-> osp osp-ancestors last)
        refined-root-osp (get-subproblem-root-pointer new-input-set (-> osp :subproblem :action)
                                                      #(root-osp osp-status :max-reward))]
    (if (identical? root-osp refined-root-osp)
      osp
      refined-root-osp)))


;; TODO: where does old reward bound go?  Wrapped-osp?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Plans ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defrecord PlanNode [input-set input-status sub-output-set-pointer excluded-child-set output-constraint status-bound])

(defn make-plan-node [input-set input-status sub-output-set-pointer excluded-child-set ouptut-constraint status-bound]
  (PlanNode. input-set input-status sub-output-set-pointer excluded-child-set ouptut-constraint status-bound))

(defn make-initial-plan-node [action [input-set input-status]]
  (let [sub (get-subproblem-root-pointer input-status action (constantly is/pos-inf))]
    (make-plan-node input-set input-status #{} {} +best-status+)))



(defn plan-node-output-set-and-status [pn]
  [(state-set/constrain
    (state/transfer-effects (:input-set pn) (:output-set (:sub-output-set-pointer pn)))
    (:output-constraint pn))
   (add-statuses
    (:input-status pn)
    (min-status (:status-bound pn) (osp-status (:sub-output-set-pointer pn))))])

(defn viable-output-set-and-status? [[set status]]
  (and (not (state-set/empty? set))
       (> (:max-reward status) is/neg-inf)))


(defn refine-pn! [pn min-reward]
  (refine-osp! (:sub-output-set-pointer pn) min-reward (:excluded-child-set pn)))

(defn split-pn-output [pn min-reward-prefix]
  (let [{:keys [input-status sub-output-set-pointer excluded-child-set]} pn]
    (let [split-children (split-osp sub-output-set-pointer (- min-reward-prefix (:max-reward input-status)) excluded-child-set)
          new-ecs        (into excluded-child-set split-children)
          new-status     (osp-status sub-output-set-pointer new-ecs)]
      (concat
       (when (> (:max-reward new-status) is/neg-inf) [(assoc pn :excluded-child-set new-ecs)])
       (for [child split-children] (assoc pn :sub-output-set-pointer child :excluded-child-set nil))))))

(defn update-pn-input [[set-changed? new-input-set new-input-status] pn]
  (let [{:keys [input-set input-status sub-output-set-pointer]} pn]
    (if (or (not set-changed?) (= new-input-set input-set))
      (if (= new-input-status input-status)
        pn
        (assoc pn :input-status new-input-status))
      (let [new-osp (refine-osp-input sub-output-set-pointer new-input-set)]
        (if (identical? new-osp sub-output-set-pointer)
          (assoc pn :input-set new-input-set :input-status new-input-status)
          (make-plan-node new-input-set new-input-status new-osp nil
                          (:output-set sub-output-set-pointer)
                          (Status. (:max-reward (osp-status sub-output-set-pointer)) :blocked)))))))




(defrecord Plan     [input-constraint plan-nodes output-set status])

(defn map-state
  "Transform a sequence via a state-machine.  transition-fn takes a state and input item,
   and returns a [state output-item] pair, or nil for reject.  Returns nil for failure,
   or a pair of the final state and output seq."
  [transition-fn init-state input-seq]
  (loop [state init-state, in-seq input-seq, out-seq []]    
    (if-let [[in-elt & more-in-seq] (seq in-seq)]
      (when-let [[next-state out-elt] (transition-fn state in-elt)]
        (recur next-state more-in-seq (conj out-seq out-elt)))
      [state out-seq])))


(defn make-initial-plan [init-set ref-constraint act-seq]
  (when-let [[[out-set out-status] plan]
             (map-state (fn [in-pair a]
                          (let [pn (make-initial-plan-node a in-pair)
                                out-pair (plan-node-output-set-and-status pn)]
                            (when (viable-output-set-and-status? out-pair)
                              [out-pair pn])))
                        [(state-set/constrain init-set ref-constraint) zero-status]
                        act-seq)]
    (Plan. ref-constraint plan out-set out-status)))



;; Remove dead plans, detect quiescense in output sets. 
(defn propagate-plan-changes
  "Returns a plan by propagating changes starting at the last node in prefix through remaining-nodes.
   Returns nil if the plan becomes infeasible, otherwise a plan."
  [input-constraint prefix-nodes remaining-nodes set-changed?]
  (when-let [chain
             (map-chain
              update-pn-input
              (cons set-changed? (plan-node-ouptut-set-and-status  (last prefix-nodes)))
              (comp viable-output-set-and-status? next)
              (fn [old-pn new-pn]
                (cons ()))
              remaining-nodes)]
    (let [[_ out-set out-status] (last chain)]
      (Plan. input-constraint (concat prefix-nodes (butlast chain)) out-set out-status))))




(defn expand-plan [plan min-reward]
  ; remove dead plans
  )






