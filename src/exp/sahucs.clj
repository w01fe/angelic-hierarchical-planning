(ns exp.sahucs
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )



;; This version may be inefficient in graphy domains, but should still be complete+optimal
;; (as long as rewards for primitives are strictly negative)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/g-pq-add! q :dummy Double/POSITIVE_INFINITY)
    (queues/pq-add-all! q initial-elements)
    q))

(defn assoc-safe [m pred k v]
  (if (contains? m k) 
    (do (assert (pred (get m k) v)) m)
    (assoc m k v)))


(defn extract-effect [state context opt]
  (vary-meta (env/extract-effects state context) assoc :opt opt))

(defn stitch-effect-map [effect-map state reward-to-state]
  (util/map-map1 
   (fn [[effects local-reward]]
     [(vary-meta (env/apply-effects state effects) assoc 
                 :opt (concat (:opt (meta state)) (:opt (meta effects))))
      (+ reward-to-state local-reward)]) 
   effect-map))

(defn stitch-state [target-state effected-state context]
  (vary-meta (env/apply-effects target-state (env/extract-effects effected-state context))
             assoc :opt (concat (:opt (meta target-state)) (:opt (meta effected-state)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 
(deftype PartialResult [queue-entries cutoff])



(deftype SANode [context action result-map-atom queue cycle-level])

(defn cutoff [node]
  (- (nth (queues/g-pq-peek-min (:queue node)) 1)))


;; Represents an action sequence from a state, with sanode representing the first action
; in remaining-actions. (or nil, if remaining-actions is empty.)
(deftype SANodeEntry [state sanode reward-to-state remaining-actions hash-code] :as this
  Object
  (equals [y] (or (identical? this y) 
                  (and (= state (:state y)) (= remaining-actions (:remaining-actions y)))))
  (hashCode [] hash-code))

(defn make-sanode-entry [state sanode reward-to-state remaining-actions]
  (SANodeEntry state sanode reward-to-state remaining-actions
               (unchecked-add (int (hash state)) 
                              (unchecked-multiply (int 13) (int (hash remaining-actions))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Algorithm  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare get-sa-node)
(defn get-sanode-entry [cache state reward-to-state actions]
  (make-sanode-entry state (when (seq actions) (delay (get-sa-node cache state (first actions)))) reward-to-state actions))

(defn lift-sanode-entry [cache entry parent-state parent-reward parent-actions context]
  (let [stitched (stitch-state parent-state (:state entry) context)]
    (SANodeEntry 
     stitched
     (or (and (seq (:remaining-actions entry)) (:sanode entry)) 
         (and (seq parent-actions) (delay (get-sa-node cache stitched (first parent-actions)))))  
     (+ (:reward-to-state entry) parent-reward)
     (concat (:remaining-actions entry) parent-actions)
     (:hash-code entry))))

(defn get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
      (let [s (env/get-logger s)
            prim? (env/primitive? a)]
        (SANode context a 
                (atom (if (and prim? (env/applicable? a s)) 
                        (let [[ss r] (env/successor a s)] {(extract-effect ss context [a]) r}) {})) 
                (make-queue (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
                              [(get-sanode-entry cache s 0.0 ref) 0.0])) 
                (hierarchy/cycle-level a s))))))


;; Q2: why do we waste effort -- should only flatten as needed.

;; Specifically, test cycle condition just before recursive expansion.
 ;; If cutoff of node is < what we would pass as next-best,
   ;; Just pull its result states, and add it back with its current cutoff.
 ;; Otherwise,
   ;; Suck everything up from its queue, integrate it, and throw it away.

;; In this version, 

;; May return states better than next-best, but these will be held at the parent.
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff dijkstra? parent-cl following-actions]
;  (println (env/action-name (:action node)) (cutoff node) last-cutoff parent-cl next-best) (util/timeout)
  (loop [new-results (if (= last-cutoff (cutoff node)) {}
                         (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
    (if (or (< (cutoff node) next-best)
            (and dijkstra? parent-cl (= parent-cl (:cycle-level node))))
        (let [state-queue-items (for [[ss sr] (stitch-effect-map new-results state reward-to-state)]
                                  [(get-sanode-entry cache ss sr following-actions) (- sr)])]
          (if (< (cutoff node) next-best)
              (PartialResult state-queue-items (cutoff node))  ;; normal termination
             (PartialResult  ;; Cycling termination.
              (concat state-queue-items
                      (for [[entry neg-rew] (queues/pq-peek-pairs (:queue node))
                            :when (< neg-rew Double/POSITIVE_INFINITY)]
                        [(lift-sanode-entry cache entry state reward-to-state following-actions (:context node)) 
                         (- neg-rew reward-to-state)]))
              Double/NEGATIVE_INFINITY)))
      (let [[entry neg-reward] (queues/g-pq-peek-min (:queue node))
            b-s (:state entry), b-rts (:reward-to-state entry), 
            b-ra (:remaining-actions entry), b-sa (force (:sanode entry))
            rec-next-best (- (max next-best (cutoff node)) b-rts)]
;        (when-not b-sa (println b-s (map env/action-name b-ra)))
        (if (empty? b-ra) ;; Optimal path to new state in output valuation found
            (let [eff (extract-effect b-s (:context node) (:opt (meta b-s)))]
;              (println "GOT STATE")
              (swap! (:result-map-atom node) assoc-safe >= eff b-rts)
              (queues/g-pq-remove!  (:queue node) entry)
              (recur (assoc-safe new-results >= eff b-rts)))
          (let [rec (expand-sa-node b-sa cache rec-next-best b-s b-rts 
                                    (- 0 neg-reward b-rts) dijkstra? (:cycle-level node) (next b-ra))]
            (if (> (:cutoff rec) Double/NEGATIVE_INFINITY) 
                (queues/g-pq-replace! (:queue node) entry (- 0 b-rts (:cutoff rec)))
              (queues/g-pq-remove!  (:queue node) entry))
            (queues/pq-add-all! (:queue node) (:queue-entries rec))
            (recur new-results)))))))

;              (and dijkstra? (:cycle-level node)    ;; Potential cycler -- suck entire queue from best-child and drop it
;                   (= (:cycle-level node) (:cycle-level b-sa))
;                   (>= (cutoff b-sa) rec-next-best))
;                (do (queues/g-pq-remove!  (:queue node) entry)
;                    
;                  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahucs-top [henv dijkstra?]
  [henv dijkstra?]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        init  (env/initial-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0 last-cutoff 0]
      (let [result (expand-sa-node root cache cutoff init 0.0 last-cutoff dijkstra? nil nil)]
        (cond (not (empty? (:queue-entries result)))
              (let [[entry] (util/first-maximal-element (comp :reward-to-state first) (:queue-entries result))]
                  [(:opt (meta (:state entry))) (:reward-to-state entry)])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result) cutoff))))))


(defn sahucs [henv] (sahucs-top henv false))
(defn sahucs-dijkstra [henv] (sahucs-top henv true))

; (dotimes [i 1] (let [h (simple-taxi-hierarchy (make-random-taxi-env 2 2 1 i))] (def *h* h)   (time (println "sahtn-dijkstra" (run-counted #(sahtn-dijkstra h)))) (println)  (time (println "simple" (run-counted #(exp.sahucs-simple/sahucs-simple h)))) (println) (time (println "simple-dijkstra" (run-counted #(exp.sahucs-simple-dijkstra/sahucs-simple-dijkstra h))))  (println) (time (println "fancy-dijkstra "(run-counted #(sahucs-dijkstra h)))) (println "\n\n\n")))

