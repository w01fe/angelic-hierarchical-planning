(ns exp.sahdd
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy])
  (:import  [java.util HashMap]))

; Here, there is no real Seq character.  No real choices.  
; Note: hard (impossible?) to unify down and up.
; Best: at least have common interface, shared parts, to simplify.

; Also fancier info going up, abstracted goals, etc.  

;; Also pass in antagonistic measure ? 

;; Should fix cost-order of subproblems.
 ;; I.e., right now, even if we have a given threshold, we return all states up to that.
 ;; Should return just first state, since it represents new alternative at higher level.
 ;; Ideally, this should just fall out of proper thinking.

; Question: what is general way to do this? 
; Note: to think of this as like SAHA, always refining a given outcome state.
;    Can think: always refining *abstracted* outcome state.
;    Note key difference: in SAHA we're doing bidi, in UCS we do forward dijkstra

; Also need goal-hiding, etc. ?

; Basic difference betwen top-down and bottom-up:
 ; top-down: give me updates since X
 ; bottom-up: give me updates as you get them, only of particular form. 
 ; For now, fix this, then extend. 


; We should still (unfortunately) never close open subproblems with cycles.  

;; For now, how do we pass states up?
  ; Store index / partial list in SubproblemEntry?
  ; Store cost and loop through?
  ; Keep queue, upwards pointers? 
  ;  Ideally, have single queue, "fingers" into it in each subproblem. 
  ;   Can almost do this with lazy seqs... ?!


(defn viable? [reward cutoff]
  (and (> reward Double/NEGATIVE_INFINITY)
       (>= reward cutoff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queues ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-queue-priority [reward]
  [(- reward)])

(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/g-pq-add! q :dummy (make-queue-priority Double/NEGATIVE_INFINITY))
    (doseq [[e r] initial-elements] (queues/pq-add! q e (make-queue-priority r)))
    q))

(defn empty-queue [queue]
  (queues/pq-remove-all! queue)
  (queues/g-pq-replace! queue :dummy (make-queue-priority Double/NEGATIVE_INFINITY)))

(defn pop-queue [queue]
  (let [[best [c]] (queues/pq-remove-min-with-cost! queue)]
    [best (- c)]))

(defn queue-best-reward [queue]
  (- (first (nth (queues/g-pq-peek-min queue) 1))))


;; TODO: generalize goal condition, etc.

(defn incremental-dijkstra 
  "Expand queue items until (1) goal, or (2) (queue-cutoff queue min-reward). 
   Safe against recursive calls in expand-fn, which takes a node and min-reward and
   returns [[old-node new-reward] & [new-node reward]*]"
  [queue min-reward expand-fn goal-fn]
  (loop []
    (or (let [cutoff (queue-best-reward queue)] 
          (when (not (viable? cutoff min-reward)) cutoff)) 
        (let [[best best-reward] (pop-queue queue)]
          (or (when-let [g (goal-fn best)] [g best-reward])
              (let [next-min-reward (max min-reward (queue-best-reward queue))]
                (queues/pq-replace! queue best (make-queue-priority best-reward))
                (let [[[_ new-reward] & new-items] (expand-fn best next-min-reward)]
                  (assert (identical? _ best))
                  (queues/pq-replace! queue best (make-queue-priority new-reward))
                  (doseq [[ni nr] new-items] 
                    (queues/pq-add! queue ni (make-queue-priority nr)))
                  (recur))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Outcome maps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn generalize-outcome-pair [[outcome-state reward] gen-state reward-to-gen-state]
  [(vary-meta (env/apply-effects gen-state (env/extract-effects outcome-state)) assoc 
              :opt (concat (:opt (meta gen-state)) (:opt (meta outcome-state))))
   (+ reward reward-to-gen-state)])

(defn pretty-state [s]
  (dissoc (env/as-map (or s {})) :const))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch 
  (next-solution-or-cutoff [sp min-reward]
     "Output is [new-outcome-state reward] where reward >= min, or new threshold < min."))

(declare extract-goal-state expand-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Dijkstra Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-incremental-dijkstra-search [initial-nodes]
  (let [q (make-queue initial-nodes)]
    (reify IncrementalSearch
      (next-solution-or-cutoff [min-reward]
        (incremental-dijkstra q min-reward expand-node extract-goal-state)))))

; (util/print-debug 1 "\nRefining " (second  name) (first name) "with min-reward [" min-reward "]" "\n" (map #(vector (pretty-state (:initial-state (first %))) (map env/action-name (:remaining-actions (first %))) (next %)) (queues/pq-peek-pairs child-queue)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: split refine into PartialResult type, always give new reward -- more accurate.
;; TODO: 

(defn make-cached-search-factory
  "Return a cache-fn, where (cache-fn) returns fresh IncrementalSearch views on
   the IncrementalSearch input (from here on out). Not thread-safe."
  [search-problem]
  (let [result-vec-atom  (atom [])
        next-reward-atom (atom Double/POSITIVE_INFINITY)]
    (fn cache-factory []
      (let [index-atom   (atom 0)]
        (reify IncrementalSearch
          (next-solution-or-cutoff [min-reward]
            (if (< @index-atom (count @result-vec-atom))
                (let [[_ rew :as result] (nth @result-vec-atom @index-atom)]
                  (if (>= rew min-reward)
                      (do (swap! index-atom inc) result)
                    rew))
              (if (viable? @next-reward-atom min-reward)
                  (let [result (next-solution-or-cutoff search-problem min-reward)]
                    (if (number? result)
                        (reset! next-reward-atom result)
                      (do (swap! result-vec-atom conj result)
                          (reset! next-reward-atom (nth result 1))))
                    (recur min-reward))
                @next-reward-atom))))))))
; (util/print-debug 2 "SSPC" min-reward (Thread/sleep 10))               

(def #^HashMap *problem-cache*)

(defmacro get-cached-search [name factory-expr]
  `((util/cache-with *problem-cache* ~name (make-cached-search-factory ~factory-expr))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; State-Abstracted Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-search-in-context [subsearch context-state context-reward]
  (reify IncrementalSearch
    (next-solution-or-cutoff [min-reward]
      (let [result (next-solution-or-cutoff subsearch (- min-reward context-reward))]
        (if (number? result) (+ result context-reward)
          (generalize-outcome-pair result context-state context-reward))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol SearchNode
  (extract-goal-state [se]
    "This entire node is one solution state, which is returned.")
  (expand-node        [se new-threshold]
    "Returns list of [SearchNode reward] pairs; first is always self"))

(deftype GoalNode [goal-state]
  SearchNode
  (extract-goal-state []           goal-state)
  (expand-node        [min-reward] (throw (UnsupportedOperationException.))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-sp-recursive-node)

(deftype SPRecursiveNode [name subproblem remaining-actions] :as this
  Object
  (equals [y] (= name (:name y)))
  (hashCode [] (hash name))
  SearchNode
  (extract-goal-state []  nil)
  (expand-node        [min-reward]
    (let [result (next-solution-or-cutoff subproblem min-reward)]
      (if (number? result) 
          [[this result]]
        [[this (nth result 1)]
         (make-sp-recursive-node result remaining-actions)]))))

;; TODO: lazy
(defn make-initial-sp-nodes [state action]
  (if (env/primitive? action)
    (when-let [[ss sr] (and (env/applicable? action state) (env/successor action state))]
      [[(GoalNode ss) sr]])
    (for [ref (hierarchy/immediate-refinements action state)]
      (make-sp-recursive-node [state 0] ref))))

(defn make-sp-recursive-node [[state reward] remaining-actions]
  [(if-let [[f & r] (seq remaining-actions)]
     (let [context          (env/precondition-context f state)
           state-in-context (env/extract-context state context)
           sub-name         [state-in-context (env/action-name f)]
           sup-name         [state-in-context (map env/action-name remaining-actions)]
           sp               (make-search-in-context 
                             (get-cached-search sub-name 
                               (make-incremental-dijkstra-search
                                (make-initial-sp-nodes (env/get-logger state context) f)))
                              state reward)]
       (SPRecursiveNode sup-name sp r))
     (GoalNode state))
   reward])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Drivers  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahucs-simple [henv]
  (binding [*problem-cache* (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (make-incremental-dijkstra-search (make-initial-sp-nodes init tla)) 
          result (next-solution-or-cutoff top Double/NEGATIVE_INFINITY)]
      (when (not (number? result))
        (second result)))))

;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 