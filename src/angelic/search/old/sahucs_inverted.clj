(ns w01fe.sahucs-inverted
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [queues :as queues] [debug-repl :as dr]]
            [w01fe [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap HashSet])
  )


;; The idea here is to implement the same algorithm as sahucs, but with a single global priority queue.
;; This may have less overhead, and make graph optimizations more straightforward.

;; Idea: queue items correspond to states at an sanode with no remaining actions.
;; When we pop it, we push it to all the parents, regardless of cost, and add to 
;; result-map-atom for future parents. 

;; Or, at time of first pop, snatch current parent set, order it, pop only best at a time.
;; Generate immediate refinements

;; TODO: why is it OK to do things state-based, not effect-based, here? 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn assoc-new [m k v]
  (assert (not (contains? m k)))
  (assoc m k v))

;(defn spos [s]  (try  (map #(env/get-var s %) '[[atx] [aty]]) (catch Exception e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stores a reference to a parent of an SANode.
;; state is the concrete state from the parent, reward is its reward within the parent,
;; sanode is the parent, and remaining-actions are the remaining actions.
  (deftype ParentEntry [state reward-to-state remaining-actions sanode hash-code]
    Object
    (equals [y] (and (= (map env/action-name remaining-actions) (map env/action-name (:remaining-actions y))) (identical? sanode (:sanode y))))
    (hashCode [] hash-code))

  (defn make-pe [state reward-to-state remaining-actions sanode]
    (ParentEntry state reward-to-state remaining-actions sanode
                 (unchecked-add (int (hash (map env/action-name remaining-actions)))
                                (unchecked-multiply (int 13) (System/identityHashCode sanode)))))

(comment 
  (deftype ParentEntry [state reward-to-state remaining-actions sanode hash-code]
    Object
    (equals [y] (and (= remaining-actions (:remaining-actions y)) (identical? sanode (:sanode y))))
    (hashCode [] hash-code))

  (defn make-pe [state reward-to-state remaining-actions sanode]
    (ParentEntry state reward-to-state remaining-actions sanode
                 (unchecked-add (int (hash remaining-actions))
                                (unchecked-multiply (int 13) (System/identityHashCode sanode))))))

;; Stores abstracted results of a state-action pair.  result-map-atom maps states
;; to rewards (within this anode).  parent-vec-atom is a map of parent-entries to
;; total rewards (minimum up to current position). parent-set is set of parents.
(deftype SANode [ action result-map-atom parent-vec-atom #^HashSet parent-set])

(defn make-sa-node [ a init-parent-entry ip-reward]
  (let [hs (HashSet.)]
    (.add hs init-parent-entry)
    (SANode  a (atom {}) (atom [[init-parent-entry ip-reward]]) hs )))


(defn gq-parent-key [parent-info]
  (if (= parent-info :fresh) :fresh (first (first parent-info))))

(deftype GQEntry [state reward-to-state sanode remaining-parents hash-code] :as this
    Object
    (equals [y] 
      (and (= state (:state y)) 
           (identical? sanode (:sanode y))
           (identical? (gq-parent-key remaining-parents) 
                       (gq-parent-key (:remaining-parents y)))))
    (hashCode [] hash-code))

(defn make-gqe [state reward-to-state sanode remaining-parents]
  (GQEntry state reward-to-state sanode remaining-parents
    (unchecked-add (int (hash state))
        (unchecked-multiply (int 13) 
          (unchecked-add (System/identityHashCode sanode)
            (unchecked-multiply (int 17) 
              (System/identityHashCode (gq-parent-key remaining-parents))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Algorithm  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn get-sa-node [#^HashMap cache a parent-entry pre-reward]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [s       (:state parent-entry)
        context (env/precondition-context a s)
        cache-key [(env/action-name a) (env/extract-context s context)]
        cache-val (.get cache cache-key)]
    (when cache-val (assert (<= pre-reward (second (peek @(:parent-vec-atom cache-val))))))
    (cond (and cache-val (.contains #^HashSet (:parent-set cache-val) parent-entry))
            []  
          cache-val
            (do (swap! (:parent-vec-atom cache-val) conj [parent-entry pre-reward])
                (.add  #^HashSet (:parent-set cache-val) parent-entry)
                (for [[ss sr] @(:result-map-atom cache-val)]
                  [(make-gqe ss sr cache-val [[parent-entry pre-reward]]) (- 0 pre-reward sr)]))
          :else 
            (let [s  (env/get-logger s context) ;(vary-meta  assoc :opt (:opt (meta s)))
                  nd (make-sa-node  a parent-entry pre-reward)]
              (.put cache cache-key nd)
              (if (env/primitive? a)
                  (when (env/applicable? a s)
;                    (println a s cache-val)
                    (let [[ss sr] (env/successor a s)]
                      [[(make-gqe (vary-meta ss assoc :opt [a]) sr nd :fresh) (- 0 pre-reward sr)]]))
                (apply concat
                  (for [ref (hierarchy/immediate-refinements a s)]
                    (if (empty? ref)
                        [[(make-gqe s 0 nd :fresh) (- pre-reward)]]
                      (get-sa-node cache (first ref) (make-pe s 0 (next ref) nd) pre-reward)))))))))

(defn update-parent [cache parent-entry parent-pre-reward new-state new-reward child-sanode]
  (let [new-effects (env/extract-effects new-state)
        final-state  (vary-meta (env/apply-effects (:state parent-entry) new-effects)
                                assoc :opt (concat (:opt (meta (:state parent-entry)))
                                                   (:opt (meta new-state))))
        actions      (:remaining-actions parent-entry)
        rts          (:reward-to-state parent-entry)]
    (if (empty? actions)
       [[(make-gqe final-state (+ rts new-reward) (:sanode parent-entry) :fresh)
         (- 0 parent-pre-reward new-reward)]]
      (get-sa-node cache (first actions) 
        (make-pe final-state (+ rts new-reward) (next actions) (:sanode parent-entry))
        (+ parent-pre-reward new-reward)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn sahucs-inverted [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        queue (queues/make-graph-search-pq)
        tla   (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])]
    (queues/pq-add-all! queue (get-sa-node cache tla (make-pe (env/initial-logging-state e) 0 nil nil) 0))
    (loop []
      (if (queues/g-pq-empty? queue) nil
        (let [[best neg-rew] (queues/g-pq-remove-min-with-cost! queue)] 
          (if (identical? (:action (:sanode best)) tla) ; solution state
              [(:opt (meta (:state best))) (- neg-rew)]
            (let [b-s  (:state best), b-rts (:reward-to-state best), b-sa (:sanode best)
                  [b-gp b-bp] (split-with #(= (second %) (- 0 neg-rew b-rts))
                                (if (= :fresh (:remaining-parents best))
                                    (do (swap! (:result-map-atom b-sa) assoc-new b-s b-rts)
                                        @(:parent-vec-atom b-sa))
                                  (:remaining-parents best)))] 
              (assert (seq b-gp))
              (when (seq b-bp)
                (queues/g-pq-replace! queue (make-gqe b-s b-rts b-sa b-bp) 
                                    (- 0 b-rts (second (first b-bp)))))
              (doseq [[p p-r] b-gp]
                (queues/g-pq-add-all! queue (update-parent cache p p-r b-s b-rts b-sa)))
              (recur))))))))



(comment
  user> (let [h (simple-taxi-hierarchy (make-random-taxi-env 15 15 9 1))] (println (update-in (time (run-counted #(sahtn-dijkstra h))) [0]  second)) (println (update-in (time (run-counted #(w01fe.sahucs-simple/sahucs-simple h))) [0]  second)) (println (update-in (time (run-counted #(w01fe.sahucs-simple-dijkstra/sahucs-simple-dijkstra h))) [0]  second)) (println (update-in (time (run-counted #(w01fe.sahucs-fancy-dijkstra/sahucs-fancy-dijkstra h))) [0]  second))  (println (time (run-counted #(w01fe.sahucs-inverted/sahucs-inverted h)))))
"Elapsed time: 2014.061 msecs"
[-131 75 22637 84697]
"Elapsed time: 6585.219 msecs"
[-131.0 75 6437 24393]
"Elapsed time: 3794.44 msecs"
[-131.0 75 22587 84630]
"Elapsed time: 3870.909 msecs"
[-131.0 75 6387 24326]
"Elapsed time: 1220.127 msecs"
[-131 75 6387 24326]
nil
  )

;                (util/assert-is (seq good-parents)  "%s" [(keyword? cpa-val) neg-rew (:reward-to-state best) best-rew (map second cur-parents) (env/action-name (:action (:sanode best))) (count cur-parents) (count (:parent-vec-atom (:sanode best)))])

;                    (util/assert-is (nil? (queues/g-pq-priority queue nxt)) "%s" [(:reward-to-state best) (second (first bad-parents))  (count cur-parents) (count bad-parents) (map second cur-parents) (count @(:parent-vec-atom (:sanode best)))])


(comment
  
;  Inefficient in cyclic hierarchies, expensive since lots of queues. 

;Detailed workings
;------------------------
;At top-level, keep a queue of ``entries''
;Each ``entry'' has a concrete state, reward-to-state, ``sanode'', and remaining-parents list.
;  - remaining-parents can be :fresh, whith means ..., or list of [parent-entry pre-reward]
;  - Equality based on the state, sanode identity, and identity of first parent.
;Each ``sanode'' represents a particular subproblem
; -- computing the results of a particular action from a particular (abstracted) state.
; - Contains an action, atom of results found so far, atom of [parent-entry reward] parents
; -    (set is redundant?).  Never compared on equality.
; - Redundant parent entries (i.e., from coalescence within parent) skipped.
 
;Global cache maps [action, state-in-context] pairs to sanodes.

;Each ``parent entry'' has a concrete state, reward-to-state, remaining-actions, parent sanode
; - (reward is reward *within the parent*)
; - Equality is based on remaining-actions and sanode (enough for uniqueness in context ? )
; - Represents a reference to an sanode from a parent sanode, more or less. 
;    - State in parent context, reward within parent context, remaining actions, ...
; - If we followed chain upwards, we would get particular context + cost.


;So, we have a chain of sanode --> parent --> sanode --> parent upwards. 

;Basic idea: when we discover a subproblem, we create an sanode and register ourselves as a parent.
;
;Get-sa-node
;-----------------------
;This is probably the main workhorse.  We pass in an action, parent-entry, and pre-reward.
;If the node exists
; If the parent is already known, we've found a worse path, and skip.
; Else, add the parent entry, and return queue entries for already discovered states.
;Else, create a new SA-node, and make queue entries for its children (either primitive result, or refinements left to go).
; 
;TODO: how aren't we missing intermediate states here?


;Flow
;-----------------------
;Each queue entry represents an *outcome* state for some action, in a (tail) subset of contexts discovered so far.  By default it;'s remaining parent set is just ``fresh'', meaning grab the list of contexts from the sanode on first expansion.  After that, it;'s the set of not-yet-good-enough parents.

;Pop the best state off the queue.  The reward associated it is the best reward to reach this state, in any currently established; hierarchical context.  We've discovered a new output state for some HLA, so we 
;(1) Add new queue entries for all optimal parents, by looking up cached results, and 
;  (a) adding entry for parent, if we're done there too, or
;  (b) jumping through next action / adding to notify list, if it exists, or 
;  (c) Creating a cascade of node/pe all the way to the primitive level, where we take our first step, for each refinement at each level.  

;Note, exploit canonicality of extra variables at any SA-node. 

  )