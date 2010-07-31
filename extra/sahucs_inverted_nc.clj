(ns exp.sahucs-inverted-nc
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [queues :as queues] [debug-repl :as dr]]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap HashSet])
  )


;; Idea here is cycle-avoiding version of sahucs.  
;; Each sanode can keep a set of (identityHashCodes) of all ancestors.
;; Problem: ancestor graph, ancestor adding, ...
;; So, again simplify with bottom-up approach: annotate states with sets of 
;; sanodes they've passed through, don't pass through cycles.  done.

;; TODO: right now only recognizes right-cycles.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn assoc-new [m k v]
  (assert (not (contains? m k)))
  (assoc m k v))

;(defn spos [s]  (try  (map #(state/get-var s %) '[[atx] [aty]]) (catch Exception e)))


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
        cache-key [(env/action-name a) (state/extract-context s context)]
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
            (let [s  (vary-meta (env/get-logger s) assoc :node-set  #{})
                  nd (make-sa-node context a parent-entry pre-reward)]
              (.put cache cache-key nd)
              (if (env/primitive? a)
                  (when (env/applicable? a s)
                    (let [[ss sr] (env/successor a s)]
                      [[(make-gqe (vary-meta ss assoc :opt [a] :node-set #{}) sr nd :fresh)
                        (- 0 pre-reward sr)]]))
                (apply concat
                  (for [ref (hierarchy/immediate-refinements a s)]
                    (if (empty? ref)
                        [[(make-gqe s 0 nd :fresh) (- pre-reward)]]
                      (get-sa-node cache (first ref) (make-pe s 0 (next ref) nd) pre-reward)))))))))

;; TODO: actually runs faster without union of parent-entry node-set ...
(defn update-parent [cache parent-entry parent-pre-reward new-state new-reward child-sanode]
  (let [new-effects (env/extract-effects new-state (:context child-sanode))
        parent-sa   (System/identityHashCode (:sanode parent-entry))
        final-state (vary-meta (state/apply-effects (:state parent-entry) new-effects)
                       assoc :opt (concat (:opt (meta (:state parent-entry))) 
                                          (:opt (meta new-state)))
                       :node-set (conj (clojure.set/union (:node-set (meta new-state))
                                                          (:node-set (meta (:state parent-entry)))) parent-sa))
        actions     (:remaining-actions parent-entry)
        rts         (:reward-to-state parent-entry)]
;    (print (type (:node-set (meta new-state))) " ")
    (if (contains? (:node-set (meta new-state)) parent-sa)
        nil ;(println "skip")
      (if (empty? actions)
        [[(make-gqe final-state (+ rts new-reward) (:sanode parent-entry) :fresh)
          (- 0 parent-pre-reward new-reward)]]
        (get-sa-node cache (first actions) 
          (make-pe final-state (+ rts new-reward) (next actions) (:sanode parent-entry))
          (+ parent-pre-reward new-reward))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn sahucs-inverted-nc [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        queue (queues/make-graph-search-pq)
        tla   (hierarchy/hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
    (queues/pq-add-all! queue (get-sa-node cache tla (make-pe (vary-meta (env/initial-logging-state e) assoc :node-set #{}) 0 nil nil) 0))
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
  user> (let [h (simple-taxi-hierarchy (make-random-taxi-env 15 15 9 1))] (println (update-in (time (run-counted #(sahtn-dijkstra h))) [0]  second)) (println (update-in (time (run-counted #(exp.sahucs-simple/sahucs-simple h))) [0]  second)) (println (update-in (time (run-counted #(exp.sahucs-simple-dijkstra/sahucs-simple-dijkstra h))) [0]  second)) (println (update-in (time (run-counted #(exp.sahucs-fancy-dijkstra/sahucs-fancy-dijkstra h))) [0]  second))  (println (time (run-counted #(exp.sahucs-inverted/sahucs-inverted h)))))
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