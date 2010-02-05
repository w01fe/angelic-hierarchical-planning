(ns exp.sahucs-simple-dijkstra
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


(defn extract-effect [state  opt]
  (vary-meta (env/extract-effects state ) assoc :opt opt))

(defn stitch-effect-map [effect-map state reward-to-state]
  (util/map-map1 
   (fn [[effects local-reward]]
     [(vary-meta (env/apply-effects state effects) assoc 
                 :opt (concat (:opt (meta state)) (:opt (meta effects))))
      (+ reward-to-state local-reward)]) 
   effect-map))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 
(deftype PartialResult [result-map cutoff])



(deftype SANode [state  action result-map-atom queue])

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
(defn get-sanode-entry [cache state reward-to-state actions parent-cycle-level]
  (make-sanode-entry state 
   (when (and (seq actions)
              (not (and parent-cycle-level
                        (when-let [b-level (hierarchy/cycle-level (first actions) state)] 
                          (assert (<= b-level parent-cycle-level))
                          (= b-level parent-cycle-level))))) 
     (get-sa-node cache state (first actions)))
   reward-to-state actions))

(defn get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
      (let [s (env/get-logger s context)]
        (if (env/primitive? a)
          (SANode s  a 
            (atom (if (env/applicable? a s) (let [[ss r] (env/successor a s)] {(extract-effect ss [a]) r}) {})) 
            (make-queue []))
          (SANode s  a (atom {}) (make-queue  [[(make-sanode-entry s nil 0.0 [a]) 0.0]])))))))



;; Q2: why do we waste effort -- should only flatten as needed.

;; Specifically, test cycle condition just before recursive expansion.
 ;; If cutoff of node is < what we would pass as next-best,
   ;; Just pull its result states, and add it back with its current cutoff.
 ;; Otherwise,
   ;; Suck everything up from its queue, integrate it, and throw it away.

;; May return states better than next-best, but these will be held at the parent.
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff dijkstra?]
  (let [cycle-level (and dijkstra? (hierarchy/cycle-level (:action node) (:state node)))]
    (loop [new-results (if (= last-cutoff (cutoff node)) {}
                           (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
      (if (< (cutoff node) next-best)
        (PartialResult (stitch-effect-map new-results state reward-to-state) (cutoff node))   
        (let [[entry neg-reward] (queues/g-pq-peek-min (:queue node))
              b-s (:state entry), b-rts (:reward-to-state entry), 
              b-ra (:remaining-actions entry), b-sa (:sanode entry)
              rec-next-best (- (max next-best (cutoff node)) b-rts)]
          (cond (empty? b-ra)  ;; Optimal path to new state in output valuation found
                  (let [eff (extract-effect b-s  (:opt (meta b-s)))]
                    (swap! (:result-map-atom node) assoc-safe >= eff b-rts)
                    (queues/g-pq-remove!  (:queue node) entry)
                    (recur (assoc-safe new-results >= eff b-rts)))
                (not b-sa)     ;; Dijkstra child.
                  (do ;(println "Out" (map #(env/get-var (:state node) %) '[[atx] [aty]]) (map env/action-name b-ra))
                      (doseq [ref (hierarchy/immediate-refinements (first b-ra) b-s)]
                        (queues/pq-add! (:queue node) 
                                        (get-sanode-entry cache b-s b-rts (concat ref (next b-ra)) cycle-level)
                                        (- b-rts)))
                      (queues/g-pq-remove!  (:queue node) entry)
                      (recur new-results))
                :else          ;; Normal intermediate node.
                  (let [rec (expand-sa-node b-sa cache rec-next-best b-s b-rts (- 0 neg-reward b-rts) dijkstra?)]
                    (doseq [[ss sr] (:result-map rec)]
                      (queues/g-pq-add! (:queue node) (get-sanode-entry cache ss sr (next b-ra) cycle-level) (- sr)))
                    (if (> (:cutoff rec) Double/NEGATIVE_INFINITY) 
                      (queues/g-pq-replace! (:queue node) entry (- 0 b-rts (:cutoff rec)))
                      (queues/g-pq-remove!  (:queue node) entry))
                    (recur new-results))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahucs-top [henv dijkstra?]
  [henv dijkstra?]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        init  (env/initial-logging-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0]
      (let [result (expand-sa-node root cache cutoff init 0.0 cutoff dijkstra?)]
        (cond (not (empty? (:result-map result)))
                (let [[k v] (util/first-maximal-element val (:result-map result))]
                  [(:opt (meta k)) v])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result)))))))


(defn sahucs [henv] (sahucs-top henv false))
(defn sahucs-simple-dijkstra [henv] (sahucs-top henv true))



