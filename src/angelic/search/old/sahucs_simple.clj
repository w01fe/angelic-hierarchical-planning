(ns angelic.sahucs-simple
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [angelic [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;; Simplest working version of sahucs, without any dijkstra nonsense, etc. 
;; May be faster due to fewer queue operations, etc.  (node creation is more eager),
;; although in practice this doesn't seem to be the case.

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


(defn extract-effect [state opt]
  (vary-meta (env/extract-effects state) assoc :opt opt))

(defn stitch-effect-map [effect-map state reward-to-state]
  (util/map-map1 
   (fn [[effects local-reward]]
     [(vary-meta (state/apply-effects state effects) assoc 
                 :opt (concat (:opt (meta state)) (:opt (meta effects))))
      (+ reward-to-state local-reward)]) 
   effect-map))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 
(deftype PartialResult [result-map cutoff])



(deftype SANode [ action result-map-atom queue])

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
  (make-sanode-entry state 
   (when (seq actions) (get-sa-node cache state (first actions)))
   reward-to-state actions))

(defn get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (state/extract-context s context)]
      (let [s     (env/get-logger s context)
            prim? (env/primitive? a)
            [ss r] (when-let [x (and prim? (env/applicable? a s) (env/successor a s))] x)] ;pun        
        (SANode  a 
          (atom (if ss {(extract-effect ss  [a]) r} {})) 
          (make-queue (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
                        [(get-sanode-entry cache s 0.0 ref) 0.0])))))))


;; May return states better than next-best, but these will be held at the parent.
 ; Note; must present consistent version of self for recursive calls too. 
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff]
  (loop [new-results (if (= last-cutoff (cutoff node)) {}
                         (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
     (if (< (cutoff node) next-best)
         (PartialResult (stitch-effect-map new-results state reward-to-state) (cutoff node))   
       (let [[entry neg-reward] (queues/g-pq-peek-min (:queue node))
             b-s (:state entry), b-rts (:reward-to-state entry), 
             b-ra (:remaining-actions entry), b-sa (:sanode entry)
             rec-next-best (- (max next-best (cutoff node)) b-rts)] ;; TODO: too conservative.  Prevents loops though :)
           (if (empty? b-ra)
               (let [eff (extract-effect b-s (:opt (meta b-s)))]
                 (swap! (:result-map-atom node) assoc-safe >= eff b-rts)
                 (queues/g-pq-remove!  (:queue node) entry)
                 (recur (assoc-safe new-results >= eff b-rts)))
             (let [rec (expand-sa-node b-sa cache rec-next-best b-s b-rts (- 0 neg-reward b-rts))]
               (doseq [[ss sr] (:result-map rec)]
                 (queues/g-pq-add! (:queue node) (get-sanode-entry cache ss sr (next b-ra)) (- sr)))
               (if (> (:cutoff rec) Double/NEGATIVE_INFINITY) 
                   (queues/g-pq-replace! (:queue node) entry (- 0 b-rts (:cutoff rec)))
                 (queues/g-pq-remove!  (:queue node) entry))
               (recur new-results)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(defn sahucs-simple [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        init  (env/initial-logging-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0]
      (let [result (expand-sa-node root cache cutoff init 0.0 cutoff)]
        (cond (not (empty? (:result-map result)))
                (let [[k v] (util/first-maximal-element val (:result-map result))]
                  [(:opt (meta k)) v])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result)))))))

