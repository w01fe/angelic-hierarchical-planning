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

(defn assoc-safe [m pred k v]
  (if (contains? m k) 
      (do (assert (pred (get m k) v)) m)
    (assoc m k v)))

(defn spos [s]  (try  (map #(env/get-var s %) '[[atx] [aty]]) (catch Exception e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stores a reference to a parent of an SANode.
;; state is the concrete state from the parent, reward is its reward within the parent,
;; sanode is the parent, and remaining-actions are the remaining actions.
(deftype ParentEntry [state reward-to-state remaining-actions sanode]
    Object
    (equals [y] (and (= remaining-actions (:remaining-actions y)) (identical? sanode (:sanode y))))
    (hashCode [] (unchecked-add (int (hash remaining-actions))
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

(deftype GQEntry [state reward-to-state sanode remaining-parents] :as this
    Object
    (equals [y] 
      (and (= state (:state y)) 
           (identical? sanode (:sanode y))
           (identical? (gq-parent-key remaining-parents) 
                       (gq-parent-key (:remaining-parents y)))))
    (hashCode [] 
      (unchecked-add (int (hash state))
        (unchecked-multiply (int 13) 
          (unchecked-add (System/identityHashCode sanode)
            (unchecked-multiply (int 17) 
              (System/identityHashCode (gq-parent-key remaining-parents))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Algorithm  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: sort out rewards.

(defn get-sa-node [#^HashMap cache a parent-entry pre-reward]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [s       (:state parent-entry)
        context (env/precondition-context a s)
        cache-key [(env/action-name a) (env/extract-context s context)]
        cache-val (.get cache cache-key)]
;    (println "get-sa" (env/action-name a) (when cache-val "t") (when (and cache-val (.contains (:parent-set cache-val) parent-entry)) "t") pre-reward (:reward-to-state parent-entry))
    (when cache-val (assert (<= pre-reward (second (last @(:parent-vec-atom cache-val))))))
    (cond (and cache-val (.contains (:parent-set cache-val) parent-entry))
            []  
          cache-val
            (do (swap! (:parent-vec-atom cache-val) conj [parent-entry pre-reward])
                (.add  (:parent-set cache-val) parent-entry)
;                (println "REHIT" (env/action-name (:action cache-val)) "in service of" (env/action-name (:action (:sanode parent-entry))) (count @(:result-map-atom cache-val)))              
                (for [[ss sr] @(:result-map-atom cache-val)]
                  (do ;(println "re-adding for result" (spos ss) pre-reward sr)
                      [(GQEntry ss sr cache-val [[parent-entry pre-reward]])
                       (- 0 pre-reward sr)])))
          :else 
            (let [s      (env/get-logger s)]
              (if (env/primitive? a)
                  (if (env/applicable? a s)
                      (let [[ss sr] (env/successor a (env/get-logger s ))
                            nd      (make-sa-node context a parent-entry pre-reward)]
;                  (println "app")
                        (.put cache cache-key nd)
                        [[(GQEntry ss sr nd :fresh)
                          (- 0 pre-reward sr)]])
                    (do ;(println "NA")
                      (.put cache cache-key (make-sa-node context a parent-entry pre-reward))
                      nil))
                (let [nd (make-sa-node context a parent-entry pre-reward)]
                  (.put cache cache-key nd)
                  (doall 
                   (mapcat 
                    (fn [ref] 
                      (if (empty? ref)
                        [[(GQEntry s 0 nd :fresh) (- pre-reward)]]
                        (get-sa-node cache (first ref) (ParentEntry s 0 (next ref) nd) pre-reward)))
                    (hierarchy/immediate-refinements a s)))))))))

(defn update-parent [cache parent-entry parent-pre-reward new-state new-reward child-sanode]
  (let [new-effects (env/extract-effects new-state (:context child-sanode))
        final-state  (env/apply-effects (:state parent-entry) new-effects)
        actions      (:remaining-actions parent-entry)]
;    (println "parent with" (map env/action-name actions) "for" (env/action-name (:action (:sanode parent-entry))) "from" (spos (:state (first (:parent-set (:sanode parent-entry))))))
    (if (empty? actions)
       [[(GQEntry final-state
                  (+ (:reward-to-state parent-entry) new-reward) 
                  (:sanode parent-entry) :fresh)
         (- 0 parent-pre-reward new-reward)]]
      (get-sa-node cache (first actions) 
                   (ParentEntry final-state 
                                (+ (:reward-to-state parent-entry) new-reward) 
                                (next actions) (:sanode parent-entry))
                   (+ parent-pre-reward new-reward)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn pp [q xs] 
  ;(println "adding" (count xs)) 
  (queues/pq-add-all! q xs))

(defn sahucs-inverted [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        queue (queues/make-graph-search-pq)]
    (queues/pq-add-all! queue
      (get-sa-node cache (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
                   (ParentEntry (env/initial-state e) 0 nil nil) 0))
    (loop []
      (if (queues/pq-empty? queue) nil
        (let [[best neg-rew] (queues/pq-remove-min-with-cost! queue)
;              fresh?         (= :fresh @(:remaining-parents-atom best))
;              rma            (:result-map-atom (:sanode best))
;              old-rew        (get @rma best)
              
              ]          
;            (assert (<= neg-rew 10))
 ;           (println neg-rew (queues/pq-size queue) (env/action-name (:action (:sanode best))) (spos (:state best)) (spos (:state (first (:parent-set (:sanode best))))) #_ (:state best))
            (if (nil? (:sanode (first (:parent-set (:sanode best)))))
                (- neg-rew)
              (let [init-hash   (hash best)
                    cpa-val     (:remaining-parents best)
;                    old-results @(:result-map-atom (:sanode best))
                    cur-parents (if (= :fresh cpa-val) 
                                  (do (swap! (:result-map-atom (:sanode best)) assoc-safe >=
                                             (:state best) (:reward-to-state best))
                                      @(:parent-vec-atom (:sanode best))) 
                                  cpa-val)
                    best-rew    (- 0 neg-rew (:reward-to-state best))
                    [good-parents bad-parents] (split-with #(= (second %) best-rew) cur-parents)]
;                (println (map second bad-parentsc))
                (util/assert-is (seq good-parents)  "%s" [(keyword? cpa-val) neg-rew (:reward-to-state best) best-rew (map second cur-parents) (env/action-name (:action (:sanode best))) (count cur-parents) (count (:parent-vec-atom (:sanode best)))])
;                (reset! (:remaining-parents-atom best) bad-parents)
;                (assert (not (= init-hash (hash best))))
                (when (seq bad-parents)
                  (let [nxt (GQEntry (:state best) (:reward-to-state best) (:sanode best) bad-parents)]
;                  (when-not (nil? (queues/g-pq-priority queue best))
;                    (let [on (queues/g-pq-key queue best)]
;                      (dr/debug-repl)))
                    (util/assert-is (nil? (queues/g-pq-priority queue nxt)) "%s" [(:reward-to-state best) (second (first bad-parents))  (count cur-parents) (count bad-parents) (map second cur-parents) (count @(:parent-vec-atom (:sanode best)))])
                    (queues/pq-replace! queue nxt 
                                        (- 0 (:reward-to-state best) (second (first bad-parents))))))
                (doseq [[parent parent-reward] good-parents]
                  (pp #_ queues/pq-add-all! queue
                    (update-parent cache parent parent-reward 
                                   (:state best) (:reward-to-state best) (:sanode best))))
                (recur))))))))



