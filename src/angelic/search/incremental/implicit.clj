(ns angelic.search.incremental.implicit
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
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
;; (although their reward may currently be lower, having passed it on furthers, if caching.)


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

(defn make-live-summary [max-reward] (SimpleSummary. max-reward :live nil))
(defn make-blocked-summary [max-reward] (SimpleSummary. max-reward :blocked nil))
(defn make-solved-summary [max-reward opt-sol] (SimpleSummary. max-reward :solved opt-sol))

(defn blocked? [summary]
  (and (not (live? summary))
       (not (optimal-solution summary))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Common Ops ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def +worst-summary+ (make-live-summary is/neg-inf))
(def +best-summary+  (make-solved-summary is/pos-inf []))

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
(defn min-summary [& stats] (apply max-compare (complement better-summary?) (cons +best-summary+ stats)))

(def zero-summary (SimpleSummary. 0 :solved []))
(defn add-summaries [s1 s2]
  (SimpleSummary. (+ (max-reward s1)
              (max-reward s2))
           (min-key status-val (:status s1) (:status s2))
           (when (and (= (:status s1) :solved) (= (:status s2) :solved))
             (concat (:opt-sol s1) (:opt-sol s2)))))


(defn viable-summary? [summary]
  (> (max-reward summary) is/neg-inf))

(defn refinable-summary? [stat min-reward]
  (and (= (:status stat) :live)
       (>= (max-reward stat) min-reward)))

(defn summary-solution [stat]
  (when (= (:status stat) :solved)
    (:opt-sol stat)))


(defn next-min-reward [stat min-reward]
  (min min-reward (max-reward stat)))



(defn max-thing-summary-and-next [summary-fn things]
  (if (empty? things)
    [nil +worst-summary+ +worst-summary+]
    (loop [best-thing (first things)
           best-summary (summary-fn (first things))
           next-best-summary +worst-summary+
           more-things (rest things)]
      (if-let [[next-thing & even-more-things] (seq more-things)]
        (let [next-summary (summary-fn next-thing)]
          (if (better-summary? next-summary best-summary)
            (recur next-thing next-summary best-summary even-more-things)
            (recur best-thing best-summary (max-summary next-summary next-best-summary) even-more-things)))
        [best-thing best-summary next-best-summary]))))

(defn one-operation-on-best [summary-fn1 s1 op1 summary-fn2 s2 op2 min-reward default]
  (let [[best1 summary1 ns1] (max-thing-summary-and-next summary-fn1 s1)
        [best2 summary2 ns2] (max-thing-summary-and-next summary-fn2 s2)
        best-summary     (max-summary summary1 summary2)]
    (if (not (refinable-summary? best-summary min-reward))
      default
      (if (better-summary? summary2 summary1)
        (op2 best2 (next-min-reward (max-summary ns2 summary1) min-reward))
        (op1 best1 (next-min-reward (max-summary ns1 summary2) min-reward))))))

(defn operate-on-best [summary-fn1 seq-fn1 op1 summary-fn2 seq-fn2 op2 init next-fn min-reward]
  (last
   (util/iterate-while
    #(when-let [x (one-operation-on-best summary-fn1 (seq-fn1 %) op1 summary-fn2 (seq-fn2 %) op2 min-reward nil)]
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

;; A subproblem represents an input-set, action pair.  All of its actual computations are organized
;; by the output set lattice.  For now, output-set-cache is not used.

(def #^HashMap *subproblem-cache* nil)

;; output-set-cache currently not used. 
(defrecord Subproblem [input-set input-context action ^HashMap output-set-cache])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Trees ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OSP trees contain pointers, which are permenant things representing a SAS combo,
;; and nodes, which contain the current state of the search (including links to child pointers).

;; TODO: put back summary caching!

; Dependencies on plans
(declare make-initial-plan expand-plan)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dependencies on pointers
(declare full-osp-summary refine-osp! add-plans-osp! make-child-osp )

(defrecord OutputSetNode    [plans child-pointers])

(defn make-initial-output-set-node [init-set action opt-reward]
  (OutputSetNode.
   (lazy-seq (for [[constraint ref] (angelic/immediate-refinements-set action init-set)
                   :let [p (make-initial-plan init-set constraint ref)] :when p]
               p))
;   (make-live-summary opt-reward)
;   +worst-summary+
   nil))
;; TODO: summaries making it into child-pointers


(defn osn-plan-summary [osn] (apply max-summary (map :summary (:plans osn))))
(defn osn-child-summary [osn ecs] (apply max-summary (map full-osp-summary (remove ecs (:child-pointers osn)))))
(defn osn-summary [osn ecs] (max-summary (osn-plan-summary osn) (osn-child-summary osn ecs)))

(def osn-child-pointers :child-pointers)
(defn osn-add-plans [osn plans] (update-in osn [:plans] concat plans))

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
        other-plans (remove #(identical? % best-plan) plans)]
    (OutputSetNode.
     (concat (new-plans output-set) other-plans)
     (merge-children parent-osp osn (dissoc new-plans output-set)))))

(defn refined-osn
  "Repeatedly refine plans stored at this osn or below."
  [osn min-reward excluded-child-set subproblem output-set]
  (operate-on-best
   :summary    :plans                     #(refine-osn-plan osn %1 %2 subproblem output-set)
   full-osp-summary #(remove excluded-child-set (:child-pointers %)) #(do (refine-osp! %1 %2) %1)
   osn identity min-reward))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Pointers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol OSP
  (osp-summary [osp excluded-child-set])
  (osp-output-set [osp]))

(defn full-osp-summary [osp]
  (osp-summary osp nil))

(defrecord TerminalOutputSetPointer [summary output-set]
  OSP
  (osp-summary [osp ecs] (assert (empty? ecs)) summary)
  (osp-output-set [osp] output-set))

(def +worst-osp+ (TerminalOutputSetPointer. +worst-summary+ state-set/empty-lfss))

(declare active-osp-summary)
(defrecord OutputSetPointer [subproblem parent-pointer output-set node-atom alt-summary]
  OSP
  (osp-summary [osp ecs] (active-osp-summary osp ecs))
  (osp-output-set [osp] output-set))


(defn make-child-osp [parent-osp output-set plans]
  (OutputSetPointer. (:subproblem parent-osp) parent-osp output-set (OutputSetNode. plans nil) +best-summary+))

(defn osp-ancestors [osp]
  (when-let [p (:parent-pointer osp)]
    (cons p (lazy-seq (osp-ancestors osp)))))

(defn osp-plan-summary [osp] (osn-plan-summary @(:node-atom osp)))

;; Used when deciding when to split.
(defn osp-descendent-summary [osp excluded-child-set]
  (min-summary (:alt-summary osp)
               (osn-summary @(:node-atom osp) excluded-child-set)))

(defn osp-ancestor-summary [osp]
  (apply max-summary (map osn-plan-summary (osp-ancestors osp))))


(defn active-osp-summary [osp excluded-child-set]
  (min-summary (:alt-summary osp)
              (max-summary (osp-descendent-summary osp excluded-child-set)
                           (osp-ancestor-summary osp))))


(defn refine-osp!
  "Repeatedly refine an ancestor or descendent of this node."
  [osp min-reward excluded-child-set]
  (operate-on-best
   osp-plan-summary osp-ancestors refine-osp!
   #(osp-summary % excluded-child-set) (constantly [osp]) #(swap! (:node-atom osp) refined-osn %2 excluded-child-set (:subproblem osp) (:output-set osp))
   osp identity min-reward))

(defn add-plans-osp!
  "Add plans from map and return map with them removed"
  [osp plans-by-output-set]
  (if-let [plans (get plans-by-output-set (:output-set osp))]
    (do (swap! (:node-atom osp) osn-add-plans plans)
        (dissoc plans-by-output-set (:output-set osp)))
    plans-by-output-set))

(defn split-osp
  "Return new-child-osps.  Currently splits children >= min-reward when parent < min-reward."
  [osp min-reward excluded-child-set]
  (when (< (max-reward (max-summary (osp-plan-summary osp) (osp-ancestor-summary osp))) min-reward)
    (filter #(>= (max-reward (full-osp-summary %)) min-reward)
            (remove excluded-child-set (osn-child-pointers @(:node-atom osp))))))

(defn can-split-osp? [osp excluded-child-set]
  (> (apply max is/neg-inf (map (comp max-reward #(osp-descendent-summary % #{}))
                                (remove excluded-child-set (osn-child-pointers @(:node-atom osp)))))
     (max-reward (max-summary (osp-plan-summary osp) (osp-ancestor-summary osp)))))




;;;;;;;;;;;;;;;;;;;;;;; Making and Splitting Subproblems ;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: terminal (solution) if concrete & primitive,
;;       termianl (blocked) if primitive or cannot refine from current set.
(defn make-subproblem [logged-input-set state-context action reward-bound-fn]
  (let [prim?        (env/primitive? action)]
    (if-let [s (and prim? (state-set/singleton logged-input-set))]
      (if (env/applicable? action s)
        (let [[ss rew] (env/successor action s)]
          (TerminalOutputSetPointer.
           (make-solved-summary rew [action])
           (state-set/make-logging-factored-state-set [ss])))
        +worst-osp+)
      (let [[opt rew]    (angelic/optimistic-set-and-reward action logged-input-set)
            rew          (min (or rew is/neg-inf) (reward-bound-fn))]
        (if (or (= rew is/neg-inf) prim? (not (angelic/can-refine-from-set? action logged-input-set)))
          (TerminalOutputSetPointer. (make-blocked-summary rew) opt)
          (let [subproblem   (Subproblem. logged-input-set state-context action (HashMap.))
                init-node    (make-initial-output-set-node logged-input-set action rew)
                init-pointer (OutputSetPointer. subproblem nil opt (atom init-node) (make-blocked-summary rew))]
;           (.put ^HashMap (:output-set-cache subproblem) opt init-pointer)
            init-pointer))))))


(defn get-subproblem-root-pointer [input-set action reward-bound-fn]
  (let [context       (env/precondition-context action input-set)
        state-context (state/extract-context input-set context)]
    ;    (println *subproblem-cache* input-set (env/action-name action) (state/get-logger input-set context) (hash [state-context (env/action-name action)]))
    (util/cache-with *subproblem-cache* [state-context (env/action-name action)] 
       (make-subproblem (state/get-logger input-set context) state-context action reward-bound-fn))))

(defn refine-osp-input [osp new-input-set]
  (let [root-osp         (-> osp osp-ancestors last)
        refined-root-osp (get-subproblem-root-pointer new-input-set (-> osp :subproblem :action)
                                                      #(-> root-osp full-osp-summary max-reward))]
    (if (identical? root-osp refined-root-osp)
      osp
      refined-root-osp)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Plans ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: available splits must contribute to live status.

(defrecord PlanNode [sub-output-set-pointer excluded-child-set output-constraint
                     summary-bound output-set output-summary])

(defn compute-plan-node-output-set [input-set sub-output-set-pointer output-constraint]
  (state-set/constrain (state/transfer-effects input-set (osp-output-set sub-output-set-pointer))
                       output-constraint))


(defn make-live-for-split [sub-osp ecs summary]
  (if (and (blocked? summary) (can-split-osp? sub-osp ecs))
    (make-live-summary (max-reward summary))
    summary))


(defn compute-plan-node-output-summary [input-summary sub-output-set-pointer ecs summary-bound]
  (->> (full-osp-summary sub-output-set-pointer)
       (min-summary summary-bound)
       (make-live-for-split sub-output-set-pointer ecs)
       (add-summaries input-summary)))

(defn make-plan-node [input-set input-summary sub-output-set-pointer
                      excluded-child-set output-constraint summary-bound]
  (PlanNode. sub-output-set-pointer excluded-child-set output-constraint summary-bound
             (compute-plan-node-output-set input-set sub-output-set-pointer output-constraint)
             (compute-plan-node-output-summary input-summary sub-output-set-pointer excluded-child-set summary-bound)))

(defn make-initial-plan-node [action [input-set input-summary]]
  (let [sub (get-subproblem-root-pointer input-set action (constantly is/pos-inf))]
    (make-plan-node input-set input-summary sub #{} {} +best-summary+)))

(defn plan-node-output-set-and-summary [pn]
  [(:output-set pn) (:output-summary pn)])

(defn viable-output-set-and-summary? [[set summary]]
  (and (not (state-set/empty? set))
       (viable-summary? summary)))


(defn refine-pn [pn input-summary min-reward]
  (let [{:keys [sub-output-set-pointer excluded-child-set summary-bound]} pn]
    (refine-osp! sub-output-set-pointer min-reward excluded-child-set)
    (assoc pn :output-summary (compute-plan-node-output-summary input-summary sub-output-set-pointer excluded-child-set summary-bound))))


(defn split-pn-output [pn input-set input-summary min-step-reward]
  (let [{:keys [sub-output-set-pointer excluded-child-set]} pn]
    (let [split-children (split-osp sub-output-set-pointer min-step-reward excluded-child-set)
          new-ecs        (into excluded-child-set split-children)
          new-summary     (osp-summary sub-output-set-pointer new-ecs)]
      (concat
       (when (viable-summary? new-summary) [(assoc pn :excluded-child-set new-ecs :output-summary new-summary)])
       (for [child split-children] (make-plan-node input-set input-summary child nil {} +best-summary+))))))

(defn patch-pn-summary-tuple- [pn new-input-summary]
  (let [{:keys [sub-output-set-pointer excluded-child-set summary-bound output-set]} pn
        new-output-summary (compute-plan-node-output-summary new-input-summary sub-output-set-pointer excluded-child-set summary-bound)]
    (when (viable-summary? new-output-summary)
      [[false output-set new-output-summary] (assoc pn :output-summary new-output-summary)])))


(defn update-pn-input [[set-changed? new-input-set new-input-summary] pn]
  (let [{:keys [sub-output-set-pointer output-constraint summary-bound output-set]} pn]
    (if set-changed?
      (let [new-osp (refine-osp-input sub-output-set-pointer new-input-set)]
        (if (identical? new-osp sub-output-set-pointer)
          (patch-pn-summary-tuple- pn new-input-summary)
          (let [new-pn (make-plan-node new-input-set new-input-summary new-osp nil
                                (osp-output-set sub-output-set-pointer)
                                (make-blocked-summary (max-reward (full-osp-summary sub-output-set-pointer)))) ;; This is just the bound, equal to the initial thing.                
                new-output-pair (plan-node-output-set-and-summary new-pn)]
            (when (viable-output-set-and-summary? new-output-pair)
              [(cons (not (= (:output-set new-pn) output-set)) new-output-pair) new-pn]))))      
      (patch-pn-summary-tuple- pn new-input-summary))))




(defrecord Plan     [input-constraint input-set plan-nodes output-set summary])

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
  (let [constrained-set (state-set/constrain init-set ref-constraint)]
    (when-let [[[out-set out-summary] plan]
              (map-state (fn [in-pair a]
                           (let [pn (make-initial-plan-node a in-pair)
                                 out-pair (plan-node-output-set-and-summary pn)]
                             (when (viable-output-set-and-summary? out-pair)
                               [out-pair pn])))
                         [constrained-set zero-summary]
                         act-seq)]
     (Plan. ref-constraint constrained-set plan out-set out-summary))))



(defn propagate-plan-changes
  "Returns a plan by propagating changes starting at the last node in prefix through remaining-nodes.
   Returns nil if the plan becomes infeasible, otherwise a plan."
  [input-constraint input-set prefix-nodes remaining-nodes set-changed?]
  (when-let [[[_ out-set out-summary] out-nodes]
             (map-state
              update-pn-input
              (cons set-changed? (plan-node-output-set-and-summary (last prefix-nodes))))]
    (Plan. input-constraint input-set (concat prefix-nodes out-nodes) out-set out-summary)))

;; Need some meta-level basis to choose what to do...
;; For now, just pick a node at random, try to refine it, then try to split on its output.
(defn expand-plan [plan min-reward]
  (let [{:keys [input-constraint input-set plan-nodes output-set summary]} plan
        [pre-nodes [ref-node & post-nodes]] (split-at (rand-int (count plan-nodes)) plan-nodes)
        [pre-set pre-summary]  (if (seq pre-nodes) (plan-node-output-set-and-summary (last pre-nodes)) [input-set zero-summary])
        sub-min-reward (- min-reward
                          (- (max-reward summary)
                             (- (max-reward (:out-summary ref-node)) (max-reward pre-summary))))]
    (filter identity
            (for [next-pn (split-pn-output (refine-pn ref-node pre-summary sub-min-reward) pre-set pre-summary sub-min-reward)]
              (propagate-plan-changes input-constraint input-set (concat pre-nodes [next-pn]) post-nodes)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top Level ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn implicit-random-dash-a* [henv]
  (let [e    (hierarchy/env henv)
        init (env-util/initial-logging-state e)
        tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
    (binding [*subproblem-cache*    (HashMap.)]
      (let [root (get-subproblem-root-pointer (state-set/make-logging-factored-state-set [init]) tla (constantly is/pos-inf))]
        (refine-osp! root is/neg-inf nil)
        (let [sum (osp-summary root nil)]
          (println sum)
          (assert (not (refinable-summary? sum is/neg-inf)))
          (when-let [sol (optimal-solution sum)]
            [sol (max-reward sum)]))))))





; (use 'edu.berkeley.ai.util '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.incremental.implicit)
; user> (require '[ angelic.search.incremental.explicit :as eis ])
;user> (eis/explicit-cn-dash-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))
;  (implicit-random-dash-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))
