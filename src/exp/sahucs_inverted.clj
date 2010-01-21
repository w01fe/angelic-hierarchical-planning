(ns exp.sahucs-inverted
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [queues :as queues] [debug-repl :as dr]]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap HashSet])
  )


;; The idea here is to implement the same algorithm as sahucs, but with a single global priority queue.
;; This may have less overhead, and make graph optimizations more straightforward.

;; Idea: queue items correspond to states at an sanode with no remaining actions.
;; When we pop it, we push it to all the parents, regardless of cost, and add to 
;; result-map-atom for future parents. 

;; Or, at time of first pop, snatch current parent set, order it, pop only best at a time.
;; Generate immediate refinements

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
    (equals [y] (and (= remaining-actions (:remaining-actions y)) (identical? sanode (:sanode y))))
    (hashCode [] hash-code))

(defn make-pe [state reward-to-state remaining-actions sanode]
  (ParentEntry state reward-to-state remaining-actions sanode
    (unchecked-add (int (hash remaining-actions))
      (unchecked-multiply (int 13) (System/identityHashCode sanode)))))

;; Stores abstracted results of a state-action pair.  result-map-atom maps states
;; to rewards (within this anode).  parent-vec-atom is a map of parent-entries to
;; total rewards (minimum up to current position). parent-set is set of parents.
(deftype SANode [context action result-map-atom parent-vec-atom #^HashSet parent-set])

(defn make-sa-node [context a init-parent-entry ip-reward]
  (let [hs (HashSet.)]
    (.add hs init-parent-entry)
    (SANode context a (atom {}) (atom [[init-parent-entry ip-reward]]) hs)))


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
            (let [s      (env/get-logger s)
                  nd     (make-sa-node context a parent-entry pre-reward)]
              (.put cache cache-key nd)
              (if (env/primitive? a)
                  (when (env/applicable? a s)
                    (let [[ss sr] (env/successor a (env/get-logger s ))]
                      [[(make-gqe ss sr nd :fresh) (- 0 pre-reward sr)]]))
                (apply concat
                  (for [ref (hierarchy/immediate-refinements a s)]
                    (if (empty? ref)
                        [[(make-gqe s 0 nd :fresh) (- pre-reward)]]
                      (get-sa-node cache (first ref) (make-pe s 0 (next ref) nd) pre-reward)))))))))

(defn update-parent [cache parent-entry parent-pre-reward new-state new-reward child-sanode]
  (let [new-effects (env/extract-effects new-state (:context child-sanode))
        final-state  (env/apply-effects (:state parent-entry) new-effects)
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
    (queues/pq-add-all! queue (get-sa-node cache tla (make-pe (env/initial-state e) 0 nil nil) 0))
    (loop []
      (if (queues/g-pq-empty? queue) nil
        (let [[best neg-rew] (queues/g-pq-remove-min-with-cost! queue)]                    
          (if (identical? (:action (:sanode best)) tla) ; solution state
              (- neg-rew)
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



;                (util/assert-is (seq good-parents)  "%s" [(keyword? cpa-val) neg-rew (:reward-to-state best) best-rew (map second cur-parents) (env/action-name (:action (:sanode best))) (count cur-parents) (count (:parent-vec-atom (:sanode best)))])

;                    (util/assert-is (nil? (queues/g-pq-priority queue nxt)) "%s" [(:reward-to-state best) (second (first bad-parents))  (count cur-parents) (count bad-parents) (map second cur-parents) (count @(:parent-vec-atom (:sanode best)))])