(ns angelic.search.incremental.implicit-dash-astar
  (:require clojure.string
            [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]             
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.util :as hierarchy-util]            
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.search.incremental.core :as is])
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

(defn make-live-summary [max-reward plan] (SimpleSummary. max-reward :live plan))
(defn make-blocked-summary [max-reward plan] (SimpleSummary. max-reward :blocked plan))
(defn make-solved-summary [max-reward opt-sol] (SimpleSummary. max-reward :solved opt-sol))

(defn blocked? [summary]
  (and (not (live? summary))
       (not (optimal-solution summary))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Common Ops ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def +worst-summary+ (make-blocked-summary is/neg-inf []))
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
;(defn min-summary [& stats] (apply max-compare (complement better-summary?) (cons +best-summary+ stats)))

(defn bound-summary [summary max-rew]
  (when (optimal-solution summary) (assert (<= (max-reward summary) max-rew)))
  (SimpleSummary. (min max-rew (:max-rew summary)) (:status summary) (:opt-sol summary)))

(defn next-min-reward [stat min-reward] (min min-reward (max-reward stat)))

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

(defn summary-str [s] (str (max-reward s) (:status s) (vec (:opt-sol s))))
(defmethod print-method SimpleSummary [s o] (print-method (summary-str s) o))

(defn assert-valid-summary-change [old-summary new-summary]
  (util/assert-is (<= (max-reward new-summary) (max-reward old-summary)) "%s" [old-summary new-summary])
  (when-not (live? old-summary) (assert (= old-summary new-summary))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Ideally, would use effect sets rather than outcome sets?  
;; TODO: make sure we are actually lazy about refinements.
;; TODO: think about loops.  In particular, loop safety.
;; TODO: think about final split.  It is probably *not* always optimal, depending on which ops you count.

;; A subproblem represents an input-set, action pair.  All of its actual computations are organized
;; by the output set lattice.  

(def #^HashMap *subproblem-cache* nil)

; Dependencies on plans
(declare make-initial-plan plan-summary plan-output-set expand-plan)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Output Set Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord OutputSetNode
  [input-pair     output-set              ; input-pair preserved (id) within a tree.
   reward-bound                           ; Outside upper bound on reward- on what TODO ???
   parent-node    ancestor-summary-atom   ; Plans directly at ancestors
   plans-atom     plan-summary-atom       ; Plans directly at node
   child-map-atom descendant-summary-atom ; Plans at descendants
   ])

(defn osn-str [osn]
  (str "OSN: " (env/action-name (second (:input-pair osn))) " " (clojure.string/join ", " (map #(summary-str (deref (% osn))) [:ancestor-summary-atom :plan-summary-atom :descendant-summary-atom]))))
(defmethod print-method OutputSetNode [osn o] (print-method (osn-str osn) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Creating ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-terminal-root-osn [input-pair output-set terminal-summary]
  (assert (not (live? terminal-summary)))
  (OutputSetNode. input-pair output-set is/pos-inf nil (atom +worst-summary+)
                  :terminal (atom terminal-summary) :terminal (atom +worst-summary+)))

(def +worst-osn+ (make-terminal-root-osn :dummy state-set/empty-lfss +worst-summary+))

(defn make-nonterminal-root-osn [input-pair output-set reward-bound init-summary init-plans]
  (assert (live? init-summary))
  (OutputSetNode. input-pair output-set reward-bound nil (atom +worst-summary+)
                  (atom init-plans) (atom init-summary) (atom {}) (atom +worst-summary+)))

(defn make-child-osn [parent-osn child-output-set]
  (OutputSetNode. (:input-pair parent-osn) child-output-set (:reward-bound parent-osn) parent-osn
                  +best-summary+ (atom nil) (atom +worst-summary+) (atom {}) (atom +worst-summary+)))



(defn make-root-osn [input-pair logged-input-set action reward-bound-fn]
  (let [prim? (env/primitive? action)]
    (if-let [s (and prim? (state-set/singleton logged-input-set))] 
      ;; terminal (solution or inapplicable) if input concrete & action primitive,
      (if (env/applicable? action s)
        (let [[ss rew] (env/successor action s)]
          (make-terminal-root-osn
           input-pair
           (state-set/make-logging-factored-state-set [ss])
           (make-solved-summary rew [action])))        
        +worst-osn+)
      (let [[opt rew]    (angelic/optimistic-set-and-reward action logged-input-set)
            rew          (min (or rew is/neg-inf) (reward-bound-fn))]
        (if (or (= rew is/neg-inf) prim? (not (angelic/can-refine-from-set? action logged-input-set)))
          ;; terminal (blocked) if primitive & non-concrete, or cannot refine, or opt. failure
          (make-terminal-root-osn
           input-pair
           opt (make-blocked-summary rew [:z action]))
          ;; finally, nonterminal if high-level, can refine, not trivially failed.
          (make-nonterminal-root-osn
           input-pair
           opt rew (make-live-summary rew nil)
           (lazy-seq (for [[constraint ref] (angelic/immediate-refinements-set action logged-input-set)
                           :let [p (make-initial-plan logged-input-set constraint ref)] :when p] p))))))))

(defn get-root-osn [input-set action reward-bound-fn]
;  (println (class action) (env/action-name action))
  (let [context    (angelic/precondition-context-set action input-set)]
    (util/cache-with *subproblem-cache* [(state/extract-context input-set context) (env/action-name action)]
       (make-root-osn [input-set action] (state/get-logger input-set context) action reward-bound-fn))))

;;    (println *subproblem-cache* input-set (env/action-name action) (state/get-logger input-set context) (hash [state-context (env/action-name action)]))




;;;;;;;;;;;;;;;;;;;;;; Computing and updating summaries ;;;;;;;;;;;;;;;;;;;;;;;;

;; Accessing mutex sets of plans.
(defn ancestor-summary   [osn] @(:ancestor-summary-atom osn))
(defn local-summary       [osn] @(:plan-summary-atom osn))
(defn descendant-summary [osn] @(:descendant-summary-atom osn))

;; Collections of plans
(defn tree-summary [osn]
  (max-summary (local-summary osn) (descendant-summary osn)))

(defn sub-descendant-summary [osn excluded-child-set]
  (if (empty? excluded-child-set) (descendant-summary osn)
      (->> osn :child-map-atom deref vals
           (remove excluded-child-set) (map tree-summary) (apply max-summary))))

(defn subtree-summary [osn excluded-child-set]
  (max-summary (local-summary osn) (sub-descendant-summary osn excluded-child-set)))

(defn handle-summary [osn]
  (max-summary (ancestor-summary osn) (local-summary osn)))

(defn broom-summary [osn excluded-child-set]
  (max-summary (ancestor-summary osn) (subtree-summary osn excluded-child-set)))

(defn root-summary [osn]
  (tree-summary (last (util/iterate-while :parent-node osn))))

;; Updating mutable fields
(defn refresh-ancestor-summary! [osn]
  (reset! (:ancestor-summary-atom osn)
          (if-let [p (:parent-node osn)]
            (max-summary (ancestor-summary p) (local-summary p))
            +worst-summary+)))

(defn refresh-local-summary! [osn]
  (reset! (:plan-summary-atom osn)
          (->> osn :plans-atom deref (map plan-summary) (apply max-summary))))

(defn refresh-descendant-summary! [osn]
  (reset! (:descendant-summary-atom osn)
          (->> osn :child-map-atom deref vals (map tree-summary) (apply max-summary))))

;; misc accessors
(def osn-output-set :output-set)
(def osn-action     (comp second :input-pair))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Refining Plans ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn get-osn-child!
  "Get or create child osn corresponding to this output-set."
  [osn child-output-set]
  (or (-> osn :child-map-atom deref (get child-output-set))
      (let [child (make-child-osn osn child-output-set)]
        (swap! (:child-map-atom osn) assoc child-output-set child)
        child)))

(defn add-plans! "Add plans, refresh summary." [osn new-plans]
;  (println (class osn))
  (swap! (:plans-atom osn) concat new-plans)
  (swap! (:plan-summary-atom osn) #(apply max-summary % (map plan-summary new-plans))))



(defn refine-osn!
  "Repeatedly refine shallowest best plan covered by osn until solved or below min-reward."
  [osn min-reward excluded-child-set]
  (while (refinable-summary? (broom-summary osn excluded-child-set) min-reward)
    (let [[[best-op] _ _ next-summary]
          (extract-best-and-summaries
           second
           [;; Ancestor
            [#(do (refine-osn! (:parent-node osn) % nil) (refresh-ancestor-summary! osn))
             (ancestor-summary   osn)]
            ;; Direct plan
            [#(let [[best-plan best-summary rest-plans rest-summary]
                      (extract-best-and-summaries plan-summary @(:plans-atom osn))
                    new-plans (expand-plan best-plan (next-min-reward rest-summary %))]
                (when-not (identical? (util/singleton new-plans) best-plan)
                  (let [grouped-plans (group-by plan-output-set new-plans)]
                   (reset! (:plans-atom osn) (concat (get grouped-plans (:output-set osn)) rest-plans))
                   (doseq [[child-output-set plans] (dissoc grouped-plans (:output-set osn))]
                     (add-plans! (get-osn-child! osn child-output-set) plans))))
                (refresh-local-summary! osn))
             (local-summary       osn)]
            ;; Descendant
            [#(let [[best-child _ _ next-summary]
                    (extract-best-and-summaries
                     tree-summary (remove excluded-child-set (vals @(:child-map-atom osn))))]
                (refine-osn! best-child (next-min-reward next-summary %) nil)
                (refresh-descendant-summary! best-child))
             (sub-descendant-summary osn excluded-child-set)]])]
      (best-op (next-min-reward next-summary min-reward)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Splitting ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn split-osn
  "Return a seq of child osn's (i.e., subset output sets) to split off from osn.
   Currently splits children >= min-reward when parent < min-reward."
  [osn min-reward excluded-child-set]
  (when (< (max-reward (handle-summary osn)) min-reward)
    (filter #(>= (max-reward (tree-summary %)) min-reward)
            (remove excluded-child-set (vals @(:child-map-atom osn))))))

(defn can-split-osn?
  "Can this OSN possibly be effectively split, at any min-reward.
   I.e., does the best plan live at a strict descendant?"
  [osn excluded-child-set]
  (> (max-reward (sub-descendant-summary osn excluded-child-set))
     (max-reward (handle-summary osn))))


(defn refine-osn-input
  "Produce a new OSN, where the input set has been restricted."
  [osn new-input-set]
  (let [new-root-osn (get-root-osn new-input-set (osn-action osn) (root-summary osn))]
    (if (identical? (:input-pair new-root-osn) (:input-pair osn)) osn new-root-osn)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Plan Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plan node is an osn in the context of a particular refinement

(defrecord PlanNode [sub-osn excluded-child-set output-constraint
                     reward-bound output-set output-summary])

(defn plan-node-str [pn]
  (str (env/action-name (osn-action (:sub-osn pn))) " (" (summary-str (:output-summary pn)) ")"))
(defmethod print-method PlanNode [pn o] (print-method (plan-node-str pn) o))



;;;;;;;;;;;;;;;;;;;;;;; Progressing sets and summaries ;;;;;;;;;;;;;;;;;;;;;;;;;

(defn compute-plan-node-output-set [input-set sub-osn output-constraint]
  (state-set/constrain (state/transfer-effects input-set (osn-output-set sub-osn))
                       output-constraint))


(defn make-live-for-split [sub-osn ecs summary]
  (if (and (blocked? summary) (can-split-osn? sub-osn ecs))
    (make-live-summary (max-reward summary) [(osn-action sub-osn)])
    summary))

(defn compute-plan-node-output-summary [input-summary sub-osn ecs reward-bound]
  (->> (broom-summary sub-osn ecs)
       (#(bound-summary % reward-bound))
       (make-live-for-split sub-osn ecs)
       (add-summaries input-summary)))


(defn plan-node-output-set-and-summary [pn]
  [(:output-set pn) (:output-summary pn)])

(defn viable-output-set-and-summary? [[set summary]]
  (and (not (state-set/empty? set))
       (viable-summary? summary)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Creating ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-plan-node [input-set input-summary sub-osn
                      excluded-child-set output-constraint reward-bound]
  (PlanNode. sub-osn excluded-child-set output-constraint reward-bound
             (compute-plan-node-output-set input-set sub-osn output-constraint)
             (compute-plan-node-output-summary input-summary sub-osn excluded-child-set reward-bound)))

(defn make-initial-plan-node [action [input-set input-summary]]
  (let [sub (get-root-osn input-set action (constantly is/pos-inf))]
    (make-plan-node input-set input-summary sub #{} {} is/pos-inf)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;; Refining Plan Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn refine-pn [pn input-summary min-reward]
  (let [{:keys [sub-osn excluded-child-set reward-bound]} pn]
    (refine-osn! sub-osn min-reward excluded-child-set)
    (let [new-summary (compute-plan-node-output-summary input-summary sub-osn
                                                        excluded-child-set reward-bound)]
      (assert-valid-summary-change (:output-summary pn) new-summary)
      (assoc pn :output-summary new-summary))))



;;;;;;;;;;;;;;;;;;;;;;;;;;; Splitting Plan Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn split-pn-output
  "Split this plan node into a seq of plan nodes, all but 0-1 of which will have
   refined output sets."
  [pn input-set input-summary min-step-reward]
  (let [{:keys [sub-osn excluded-child-set]} pn
        split-children (split-osn sub-osn min-step-reward excluded-child-set)
        _  (when (seq split-children) (println "SPLIT" pn (count split-children)))
;        _   (println "split" pn (count excluded-child-set) (count split-children))    
        new-ecs        (into excluded-child-set split-children)
        new-summary    (add-summaries input-summary (broom-summary sub-osn new-ecs))]
    (concat
     (when (viable-summary? new-summary)
       (assert-valid-summary-change (:output-summary pn) new-summary)
       [(assoc pn :excluded-child-set new-ecs :output-summary new-summary)])
     (for [child split-children]
       (do ;         (println "SC"  sub-osn child )
           (make-plan-node input-set input-summary child nil {} is/pos-inf))))))


(defn update-pn-input
  "Take a tuple describing updated inputs and a plan node, and return a tuple
   describing updated outputs and the updated plan node.  Returns nil for dead-ends."
  [[set-changed? new-input-set new-input-summary] pn]
  (let [{:keys [sub-osn excluded-child-set output-constraint reward-bound output-set]} pn
        new-osn (if set-changed? (refine-osn-input sub-osn new-input-set) sub-osn)]
    (if (identical? new-osn sub-osn)
      (let [new-output-summary (compute-plan-node-output-summary
                                new-input-summary sub-osn excluded-child-set reward-bound)]
        (assert-valid-summary-change (:output-summary pn) new-output-summary)
        (when (viable-summary? new-output-summary)
          [[false output-set new-output-summary] (assoc pn :output-summary new-output-summary)]))
      (let [new-pn (make-plan-node new-input-set new-input-summary new-osn nil
                                   (osn-output-set sub-osn)
                                   (max-reward (broom-summary sub-osn)))
            new-output-pair (plan-node-output-set-and-summary new-pn)]
        (assert-valid-summary-change (:output-summary pn) (second new-output-pair))
        (when (viable-output-set-and-summary? new-output-pair)
          [(cons (not (= (:output-set new-pn) output-set)) new-output-pair) new-pn])))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Plans ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plan is effectively a sequence of plan nodes.

(defrecord Plan     [input-constraint input-set plan-nodes output-set summary])

(defn plan-str [p]
  (clojure.string/join ", " (map plan-node-str (:plan-nodes p))))
(defmethod print-method Plan [p o] (print-method (plan-str p) o))

(def plan-summary :summary)
(def plan-output-set :output-set)



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
              (cons set-changed? (plan-node-output-set-and-summary (last prefix-nodes)))
              remaining-nodes)]
    (Plan. input-constraint input-set (concat prefix-nodes out-nodes) out-set out-summary)))

;; Need some meta-level basis to choose what to do...
;; For now, just pick a node at random, try to refine it, then try to split on its output.
(defn expand-plan [plan min-reward]
  (if (not (refinable-summary? (:summary plan) min-reward)) [plan]
      (let [{:keys [input-constraint input-set plan-nodes output-set summary]} plan
            ref-index                           (rand-int (count plan-nodes))
            [pre-nodes [ref-node & post-nodes]] (split-at ref-index plan-nodes)
;            _ (println plan  (count pre-nodes) (class ref-node) (count post-nodes))       
            [pre-set pre-summary]  (if (seq pre-nodes) (plan-node-output-set-and-summary (last pre-nodes)) [input-set zero-summary])
            sub-min-reward (- min-reward
                              (- (max-reward summary)
                                 (- (max-reward (:output-summary ref-node)) (max-reward pre-summary))))]
        (filter identity
                (for [next-pn (split-pn-output (refine-pn ref-node pre-summary sub-min-reward) pre-set pre-summary sub-min-reward)]
                  (do (assert-valid-summary-change (:output-summary ref-node) (:output-summary next-pn))
                   (propagate-plan-changes input-constraint input-set (concat pre-nodes [next-pn]) post-nodes
                                           (not= (:output-set next-pn) (:output-set ref-node)))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top Level ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn implicit-random-dash-a* [henv]
  (let [e    (hierarchy/env henv)
        init (env-util/initial-logging-state e)
        tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
    (binding [*subproblem-cache*    (HashMap.)]
      (let [root (get-root-osn (state-set/make-logging-factored-state-set [init]) tla (constantly is/pos-inf))]
        (refine-osn! root is/neg-inf nil)
        (let [sum (broom-summary root nil)]
          (println sum)
          (assert (not (refinable-summary? sum is/neg-inf)))
          (def *root* root)
          (when-let [sol (optimal-solution sum)]
            [sol (max-reward sum)]))))))





; (use 'edu.berkeley.ai.util '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.incremental.implicit)
; user> (require '[ angelic.search.incremental.explicit :as eis ])
;user> (eis/explicit-cn-dash-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))
;  (implicit-random-dash-a* (make-nav-switch-hierarchy (make-random-nav-switch-env 5 2 0) true))


 ; (do (use 'edu.berkeley.ai.util '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.incremental.implicit 'angelic.domains.discrete-manipulation) (require '[angelic.search.incremental.hierarchical :as his]))

;(let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 1 3))] (println (run-counted #(his/interactive-hierarchical-search h))) #_ (println (run-counted #(implicit-random-dash-a* h))))