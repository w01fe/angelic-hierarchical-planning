(ns angelic.sahdd
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [angelic.env :as env] 
            [angelic.hierarchy :as hierarchy])
  (:import  [java.util HashMap]))

;; TODO: note other sahucs implementations are incorrect, since they don't handle reward decreases of partial nodes properly. ?  
;; For the same reason, sahucs-fancy-dijkstra is doubly-incorrect ? 

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

;; TODO: need tests, domains with multiple outcome states. ! 

; More general ways to express sequencing, primitives?
; Ways to merge "searches" and "nodes"? 
; 
; In all of this, how do "policies" get specified.  I.e., search types for lower levels? 

  ; I.e., AHA* 


(defn viable? [reward cutoff]
  (and (> reward Double/NEGATIVE_INFINITY)
       (>= reward cutoff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queues ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-queue-priority [reward]
  [(- reward)])

(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/pq-add! q :dummy (make-queue-priority Double/NEGATIVE_INFINITY))
    (doseq [[e r] initial-elements] (queues/pq-add! q e (make-queue-priority r)))
    q))

;(defn empty-queue [queue]
;  (queues/pq-remove-all! queue)
;  (queues/g-pq-replace! queue :dummy (make-queue-priority Double/NEGATIVE_INFINITY)))

(defn pop-queue [queue]
  (let [[best [c]] (queues/pq-remove-min-with-cost! queue)]
    [best (- c)]))

(defn queue-best-reward [queue]
  (- (first (nth (queues/pq-peek-min queue) 1))))


;; TODO: generalize goal condition, etc.

(deftype PartialResult [result-pairs max-reward])

;; TODO: once we start expanding a node, it should be off-limits to reward increases
 ; ; (subject to a check that actual *initial* reward does not increase.)

(defn incremental-dijkstra 
  "Expand queue items until (1) goal, or (2) (queue-cutoff queue min-reward). 
   Safe against recursive calls in expand-fn, which takes a node and min-reward and
   returns a PartialResult of nodes."
  [new-queue partial-queue min-reward expand-fn goal-fn]
  (let [queue (queues/make-union-pq new-queue partial-queue)]
    (loop []
 ;    (println (queues/pq-size queue))
      (or (let [cutoff (queue-best-reward queue)] 
            (when (not (viable? cutoff min-reward)) (PartialResult nil cutoff))) 
          (let [[best best-reward] (pop-queue queue)]
            (or (when-let [g (goal-fn best)] (PartialResult [[g best-reward]] (queue-best-reward queue)))
                (let [next-min-reward (max min-reward (queue-best-reward queue))]
                  (queues/pq-replace! partial-queue best (make-queue-priority best-reward))
                  (let [{:keys [result-pairs max-reward]} (expand-fn best next-min-reward)]
;                    (println result-pairs max-reward)
                    (if (= max-reward Double/NEGATIVE_INFINITY) 
                        (queues/pq-remove! partial-queue best)
                      (queues/pq-replace! partial-queue best (make-queue-priority max-reward)))
                    (doseq [[ni nr] result-pairs] 
;                      (util/assert-is (not (nil? nr)) "%s" (def badd (vec result-pairs)))
 ;                    (println "NEW" max-reward (class ni) nr (:name ni))
                      (assert (not (= :re-added (queues/pq-add! new-queue ni (make-queue-priority nr))))))
                    (recur)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Outcome maps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn generalize-outcome-pair [[outcome-state reward] gen-state reward-to-gen-state]
  [(vary-meta (state/apply-effects gen-state (env/extract-effects outcome-state)) assoc 
              :opt (concat (:opt (meta gen-state)) (:opt (meta outcome-state))))
   (+ reward reward-to-gen-state)])

(defn pretty-state [s]
  (dissoc (state/as-map (or s {})) :const))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol IncrementalSearch 
  (next-partial-solution [sp min-reward]
     "Output is PartialResult, where results are states."))

(declare extract-goal-state expand-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Dijkstra Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-incremental-dijkstra-search [initial-nodes]
;  (println "Creating new search.")
  (let [new-q (make-queue initial-nodes) partial-q (make-queue nil)]
    (reify IncrementalSearch
           (next-partial-solution [min-reward]
             (incremental-dijkstra new-q partial-q min-reward expand-node extract-goal-state)))))



;; TODO: need "generalized-goal" dijkstra search.  
;; TODO: single-goal.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Exhaustive Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No reason to use this except to emulate SAHTN.
;; Note: destroys cost order, but should still work correctly.

(defn make-exhaustive-search [sp]
  (reify IncrementalSearch
    (next-partial-solution [min-reward]
;      (println "Entering")
      (loop [results []]
        (let [{:keys [result-pairs max-reward]} (next-partial-solution sp Double/NEGATIVE_INFINITY)]
;          (println "Got results " (map (juxt (comp pretty-state first) second) result-pairs) max-reward)
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
                 ;; TODO: remove
;                  (util/assert-is (<= (count @result-vec-atom) 1) "%s" [@result-vec-atom])
                  (if (>= rew min-reward)
                      (do (swap! index-atom inc) 
                          (PartialResult [result] 
                                         (max (second (get @result-vec-atom @index-atom [nil Double/NEGATIVE_INFINITY])) 
                                              @next-reward-atom)))
                    (PartialResult nil rew)))
              (if (viable? @next-reward-atom min-reward)
                  (let [{:keys [result-pairs max-reward]} (next-partial-solution search-problem min-reward)]
                    (reset! next-reward-atom max-reward)
                    ;; TODO: remove!
 ;                   (doseq [x1 @result-vec-atom x2 result-pairs] 
 ;                     (util/assert-is (not (= (first x1) (first x2))) "%s" [@result-vec-atom result-pairs]))
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




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; State-Action searches ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-search-node)

(defn make-incremental-dijkstra-sa-search [state action]
  (make-incremental-dijkstra-search [(make-search-node :transparent [state action] [state 0] [action])]))

(defn make-abstracted-incremental-dijkstra-sa-search [state reward action]
  (let [context (env/precondition-context action state)]
    (make-search-in-context 
     (get-cached-search [(state/extract-context state context) (env/action-name action)] 
       (make-incremental-dijkstra-sa-search (env/get-logger state context) action))
     state reward)))


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
   (extract-goal-state [] goal-state)
   (expand-node        [min-reward] (throw (UnsupportedOperationException.))))

;; Named node is simple non-terminal node whose equality semantics are given by name.
(deftype NamedNode [name root-sa expand-fn] :as this
  Object
  (equals [y] (= name (:name y)))
  (hashCode [] (hash name))
  SearchNode
  (extract-goal-state []  nil)
  (expand-node        [min-reward] (expand-fn root-sa min-reward)))


(def *node-type-policy* (fn [root-sa state first-action] :unknown))

(defn make-node-descendant [root-sa [state reward :as result] remaining-actions]
  (make-search-node (when-first [f remaining-actions] (*node-type-policy* root-sa state f))
                    root-sa result remaining-actions))

(defn make-recursive-expander [sp more-actions]
  (fn sp-recursive-expand [root-sa min-reward]
      (let [{:keys [result-pairs max-reward]} (next-partial-solution (force sp) min-reward)]
        (PartialResult (map #(make-node-descendant root-sa % more-actions) result-pairs) max-reward))))


(defn make-search-node [type root-sa [state reward :as result] remaining-actions]
;  (println "making node" [state (map env/action-name remaining-actions)]) 
;  (Thread/sleep 100)
  [(if-let [[f & r] (seq remaining-actions)]
       (NamedNode [state (map env/action-name remaining-actions)] root-sa
         (case type
          :transparent          
            (fn sp-transparent-expand [root-sa min-reward]
              (PartialResult
               (if (env/primitive? f)
                 (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
                   [(make-node-descendant root-sa [(vary-meta ss assoc :opt [f]) (+ sr reward)] r)])
                 (for [ref (hierarchy/immediate-refinements f state)]
                   (make-node-descendant root-sa [state reward] (concat ref r))))
               Double/NEGATIVE_INFINITY))
          :recursive            
            (make-recursive-expander 
             (delay (make-abstracted-incremental-dijkstra-sa-search state reward f)) r)          
          :recursive-exhaustive 
            (make-recursive-expander 
             (delay (make-exhaustive-search 
                     (make-abstracted-incremental-dijkstra-sa-search state reward f))) r)))
     (GoalNode state))
   reward])





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Semi-Transparent Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Need method on search to return node-list to implement this...
(defn make-sp-semi-transparent-node [[state reward] remaining-actions]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Inverted Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: Rewards passed around are all global-best.

;; Can we do it as "state-to-go", not "finished state" ?
; i.e., state, reward, remaining-actions, parent-cache.
; when r-a is empty, update.  Can add factoring later if we need it ? 

;; Note: can we cache results across calls? 
;; We need same initial state, at least. 
;;  Different goal is possible, but might as well integrate this above as well. 

;; TODO: think about IDA* 

;; TODO: unify, allowing other searches below --> expand-node must use min-reward. ?



;; TODO: remove expensive tests.
(defn- add-monotonic! [result-pair-atom [new-result new-reward :as new-result-pair]]
  (assert (every? #(not (= (first %) new-result)) @result-pair-atom))
  (when (seq @result-pair-atom) (assert (<= new-reward (second (last @result-pair-atom)))))
  (swap! result-pair-atom conj new-result-pair))

(defprotocol InvertedItem (notify-upward [item outcome-pair]))

(deftype InvertedCache [result-pairs-atom parent-pairs-atom base-reward]
  InvertedItem 
    (notify-upward [outcome-pair]
      (add-monotonic! result-pairs-atom outcome-pair)
      (let [[outcome rew] outcome-pair ]
        (mapcat (fn [[parent parent-rew :as parent-pair]]
                  (notify-upward parent [outcome (+ rew (- parent-rew base-reward))]))
                @parent-pairs-atom))))

(declare make-inverted-node)

(defn connect-downward-cache [#^HashMap cc state action [new-parent new-reward :as new-parent-pair]]
  (let [context (env/precondition-context action state)
        ic      (util/cache-with cc [(state/extract-context state context) (env/action-name action)]
                  (InvertedCache (atom []) (atom []) new-reward))
        {:keys [result-pairs-atom parent-pairs-atom base-reward]} ic 
        first-visit?  (empty? @parent-pairs-atom)]
    (add-monotonic! parent-pairs-atom new-parent-pair)
    (if first-visit?  ; first time: create and return sub-nodes.
        (let [state (env/get-logger state context)]
          (if (env/primitive? action)
              (when-let [[ss sr] (and (env/applicable? action state) (env/successor action state))]
                [(make-inverted-node cc (vary-meta ss assoc :opt [action]) (+ base-reward sr) nil ic)])
            (for [ref (hierarchy/immediate-refinements action state)]
              (make-inverted-node cc state base-reward ref ic))))
      (mapcat (fn [[outcome outcome-rew]]
                (notify-upward new-parent [outcome (+ outcome-rew (- new-reward base-reward))]))
              @result-pairs-atom))))


;; TODO: partial expansions for goals ? 
(deftype InvertedNode   [cache-cache name state reward remaining-actions parent-cache] :as this
  Object
   (equals   [y] (= name (:name y)))
   (hashCode []  (hash name))
  SearchNode
   (extract-goal-state [] nil)
   (expand-node        [min-reward]
     (PartialResult                   
      (if-let [[f] (seq remaining-actions)]
          (connect-downward-cache cache-cache state f [this reward])
        (notify-upward parent-cache [state reward]))
      Double/NEGATIVE_INFINITY ))
  InvertedItem 
   (notify-upward [outcome-pair]
     (let [[outcome-state outcome-rew] (generalize-outcome-pair outcome-pair state 0)]
       [(make-inverted-node cache-cache outcome-state outcome-rew (next remaining-actions) parent-cache)])))

(defn make-inverted-node [cc state reward remaining-actions parent-cache]
  [(InvertedNode cc [state remaining-actions parent-cache] state reward remaining-actions parent-cache) reward])

(defn make-inverted-roots [state action]
  (connect-downward-cache (HashMap.) state action 
    [(reify InvertedItem 
       (notify-upward [outcome-pair]  [(update-in outcome-pair [0] GoalNode)])) 
     0]))

(defn make-inverted-sa-search [state action]
  (make-incremental-dijkstra-search (make-inverted-roots state action)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn hierarchical-search [henv policy search-maker]
  (binding [*node-type-policy* policy
            *problem-cache*    (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (search-maker init tla)]
      (when-let [[s r] (first (:result-pairs (next-partial-solution top Double/NEGATIVE_INFINITY)))]
        [(map env/action-name (:opt (meta s))) r ]))))

(defn if-cycle-fn [if-cycle else]
  (fn [[parent-state parent-action] state action]
    #_(println (env/action-name action) (hierarchy/cycle-level action state)
             (env/action-name (:action parent)) (hierarchy/cycle-level (:action parent) (:state parent)))
    (if (util/aand (hierarchy/cycle-level action state)
                   (= it (hierarchy/cycle-level parent-action parent-state)))
        if-cycle else)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Drivers   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahtn-simple [henv]
  (hierarchical-search henv (constantly :recursive-exhaustive)
    (comp make-exhaustive-search make-incremental-dijkstra-sa-search)))

(defn sahtn-dijkstra [henv]
  (hierarchical-search henv (if-cycle-fn :transparent :recursive-exhaustive) 
    (comp make-exhaustive-search make-incremental-dijkstra-sa-search)))


(defn sahucs-flat [henv]
  (hierarchical-search henv (constantly :transparent)
    make-incremental-dijkstra-sa-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv (constantly :recursive)
    make-incremental-dijkstra-sa-search))

(defn sahucs-dijkstra [henv]
  (hierarchical-search henv (if-cycle-fn :transparent :recursive) 
    make-incremental-dijkstra-sa-search))

(defn sahucs-inverted [henv]
  (hierarchical-search henv :dummy
    make-inverted-sa-search))



(comment
 (let [e (make-random-taxi-env 3 3 3 2) h (simple-taxi-hierarchy e)]  
  (println "ucs" (run-counted #(second (uniform-cost-search e))))
  (doseq [alg `[sahtn-dijkstra sahucs-flat sahucs-simple sahucs-dijkstra sahucs-inverted]]
         (time (println alg (run-counted #(second ((resolve alg) h)))))))
 )


;; TODO: compare performance to other algorithms.  


;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 