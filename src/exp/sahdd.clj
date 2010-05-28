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

(deftype PartialResult [result-pairs max-reward])

(defn incremental-dijkstra 
  "Expand queue items until (1) goal, or (2) (queue-cutoff queue min-reward). 
   Safe against recursive calls in expand-fn, which takes a node and min-reward and
   returns a PartialResult of nodes."
  [queue min-reward expand-fn goal-fn]
  (loop []
    (or (let [cutoff (queue-best-reward queue)] 
          (when (not (viable? cutoff min-reward)) (PartialResult nil cutoff))) 
        (let [[best best-reward] (pop-queue queue)]
          (or (when-let [g (goal-fn best)] (PartialResult [[g best-reward]] (queue-best-reward queue)))
              (let [next-min-reward (max min-reward (queue-best-reward queue))]
                (queues/pq-replace! queue best (make-queue-priority best-reward))
                (let [{:keys [result-pairs max-reward]} (expand-fn best next-min-reward)]
                  (queues/pq-replace! queue best (make-queue-priority max-reward))
                  (doseq [[ni nr] result-pairs] 
                    (queues/pq-add! queue ni (make-queue-priority nr)))
                  (recur))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Outcome maps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-descendents [state action prim-constructor ref-constructor]
  (if (env/primitive? action)
      (when-let [[ss sr] (and (env/applicable? action state) (env/successor action state))]
        [(prim-constructor (vary-meta ss assoc :opt [action]) sr)])
    (map ref-constructor (hierarchy/immediate-refinements action state))))

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
  (next-partial-solution [sp min-reward]
     "Output is PartialResult, where results are states."))

(declare extract-goal-state expand-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Dijkstra Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-incremental-dijkstra-search [initial-nodes]
  (let [q (make-queue initial-nodes)]
    (reify IncrementalSearch
      (next-partial-solution [min-reward]
        (incremental-dijkstra q min-reward expand-node extract-goal-state)))))


;; TODO: need "generalized-goal" dijkstra search.  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No reason to use this except to emulate SAHTN.
;; Note: destroys cost order, but should still work correctly.

(defn make-exhaustive-search [sp]
  (reify IncrementalSearch
    (next-partial-solution [min-reward]
      (loop [results []]
        (let [{:keys [result-pairs max-reward]} (next-partial-solution sp Double/NEGATIVE_INFINITY)]
          (let [next-results (into results result-pairs)]
            (if (= max-reward Double/NEGATIVE_INFINITY)
                (PartialResult next-results max-reward)
              (recur next-results))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Cached Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-cached-search-factory
  "Return a cache-fn, where (cache-fn) returns fresh IncrementalSearch views on
   the IncrementalSearch input (from here on out). Not thread-safe."
  [search-problem]
  (let [result-vec-atom  (atom [])
        next-reward-atom (atom Double/POSITIVE_INFINITY)]
    (fn cache-factory []
      (let [index-atom   (atom 0)]
        (reify IncrementalSearch
          (next-partial-solution [min-reward]
            (if (< @index-atom (count @result-vec-atom))
                (let [[_ rew :as result] (nth @result-vec-atom @index-atom)]
                  (if (>= rew min-reward)
                      (do (swap! index-atom inc) 
                          (PartialResult [result] 
                                         (max (get @result-vec-atom @index-atom Double/NEGATIVE_INFINITY) 
                                              @next-reward-atom)))
                    (PartialResult nil rew)))
              (if (viable? @next-reward-atom min-reward)
                  (let [{:keys [result-pairs max-reward]} (next-partial-solution search-problem min-reward)]
                    (reset! next-reward-atom max-reward)
                    (swap!  result-vec-atom into result-pairs)
                    (recur min-reward))
                (PartialResult nil @next-reward-atom)))))))))

(def #^HashMap *problem-cache*)

(defmacro get-cached-search [name factory-expr]
  `((util/cache-with *problem-cache* ~name (make-cached-search-factory ~factory-expr))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; State-Abstracted Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn lift-partial-result [partial-result context-state context-reward]
  (let [{:keys [result-pairs max-reward]} partial-result]
    (PartialResult (map #(generalize-outcome-pair % context-state context-reward) result-pairs)
                   (+ max-reward context-reward))))

(defn make-search-in-context [subsearch context-state context-reward]
  (reify IncrementalSearch
    (next-partial-solution [min-reward]
      (lift-partial-result (next-partial-solution subsearch (- min-reward context-reward))
                           context-state context-reward))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defprotocol SearchNode
  (extract-goal-state [se]
    "This entire node is one solution state, which is returned.")
  (expand-node        [se new-threshold]
    "Returns PartialResult of SearchNodes."))

(deftype GoalNode [goal-state]
  SearchNode
  (extract-goal-state []           goal-state)
  (expand-node        [min-reward] (throw (UnsupportedOperationException.))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Named Node (Helper) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Named node is simple non-terminal node whose equality semantics are given by name.
(deftype NamedNode [name expand-fn] :as this
  Object
  (equals [y] (= name (:name y)))
  (hashCode [] (hash name))
  SearchNode
  (extract-goal-state []  nil)
  (expand-node        [min-reward] (expand-fn min-reward)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-sp-recursive-node)

(defn make-initial-sp-nodes [state action]
  (make-descendents state action 
    (fn [ss sr] [(GoalNode ss) sr]) 
    (fn [ref] (make-sp-recursive-node [state 0] ref))))    

(defn make-sp-recursive-node [[state reward] remaining-actions]
  [(if-let [[f & r] (seq remaining-actions)]
     (let [context (env/precondition-context f state)
           sp      (delay 
                    (make-search-in-context 
                     (get-cached-search [(env/extract-context state context) (env/action-name f)] 
                       (make-incremental-dijkstra-search
                        (make-initial-sp-nodes (env/get-logger state context) f)))
                     state reward))]
       (NamedNode [state (map env/action-name remaining-actions)] 
          (fn sp-recursive-expand [min-reward]
            (let [{:keys [result-pairs max-reward]} (next-partial-solution (force sp) min-reward)]
              (PartialResult (map #(make-sp-recursive-node % r) result-pairs) max-reward)))))   
     (GoalNode state))
   reward])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Transparent Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-sp-transparent-node [[state reward] remaining-actions]
  [(if-let [[f & r] (seq remaining-actions)]
       (NamedNode [state (map env/action-name remaining-actions)]
         (fn sp-transparent-expand [min-reward]
           (PartialResult
            (make-descendents state f 
              (fn [ss sr] (make-sp-transparent-node [ss (+ sr reward)] r))
              (fn [ref]   (make-sp-transparent-node [state reward] (concat ref r))))
            Double/NEGATIVE_INFINITY)))
     (GoalNode state))
   reward])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Semi-Transparent Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Need method on search to return node-list to implement this...
(defn make-sp-semi-transparent-node [[state reward] remaining-actions]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Inverted Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: how to switch between these as we go?!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Drivers  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn hierarchical-search [henv search-maker]
  (binding [*problem-cache* (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (search-maker init tla)]
      (when-let [[s r] (first (:result-pairs (next-partial-solution top Double/NEGATIVE_INFINITY)))]
        [(map env/action-name (:opt (meta s))) r ]))))

(defn sahucs-simple [henv]
  (hierarchical-search henv (fn [s a] (make-incremental-dijkstra-search (make-initial-sp-nodes s a)))))




(defn blablabla [henv]
  (binding [*problem-cache* (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (make-incremental-dijkstra-search (make-initial-sp-nodes init tla))]
      (next-partial-solution (make-exhaustive-search top) Double/NEGATIVE_INFINITY))))

(defn sahucs-transparent [henv]
  (binding [*problem-cache* (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (make-incremental-dijkstra-search [(make-sp-transparent-node [init 0] [tla])]) 
          result (next-partial-solution top Double/NEGATIVE_INFINITY)]
      (assert (< (count (:result-pairs result 1))))
      (second (first (:result-pairs result))))))

;; TODO: compare performance to other algorithms.  


;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 