(ns exp.sahucs
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHD
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version may be inefficient in graphy domains, but should still be complete+optimal
;; (as long as rewards for primitives are strictly negative)

;; TODO: pass incremental updates upwards. 
;; Difficulty: nodes with multiple ancestors.

(defprotocol HasCutoff (cutoff [x]))
(defprotocol HasQueue  (queue [x]))

(deftype PartialResult [result-map cutoff]
  HasCutoff (cutoff [] cutoff))


;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 


(deftype SANode [context action result-map-atom queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue))))
  HasQueue  (queue [] queue))

;; Represents an action sequence from a state, with sanode representing the first action in remaining-actions.
 ; (or nil, if remaining-actions is empty.)
(deftype SANodeEntry [state sanode reward-to-state remaining-actions]
  Object
   (equals [y] (and (= state (:state y)) (= remaining-actions (:remaining-actions y))))
   (hashCode [] (unchecked-add (int (hash state)) 
                               (unchecked-multiply (int 13) (int (hash remaining-actions))))))


(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/pq-add! q :dummy Double/POSITIVE_INFINITY)
    (queues/pq-add-all! q initial-elements)
    q))

(defn assoc-safe [m pred k v]
  (if (contains? m k) 
    (do (assert (pred (get m k) v)) m)
    (assoc m k v)))

; empty refinement !

(defn- get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
;  (println "GET SA" (env/action-name a))
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
      (let [s     (env/get-logger s)
            prim? (env/primitive? a)
            [ss r] (when-let [x (and prim? (env/applicable? a s) (env/successor a s))] x)] ;pun        
        (SANode context a 
          (atom (if ss {(vary-meta (env/extract-effects ss context) assoc :opt [a]) r} {})) 
          (make-queue (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
                        [(SANodeEntry s (when (seq ref) (get-sa-node cache s (first ref))) 0.0 ref) 0.0])))))))



(defn stitch-results [effect-map state reward-to-state]
  (util/map-map 
   (fn [[effects local-reward]]
     [(vary-meta (env/apply-effects state effects) assoc :opt (concat (:opt (meta state)) (:opt (meta effects))))
      (+ reward-to-state local-reward)]) 
   effect-map))

;; May return states better than next-best, but these will be held at the parent.
(defn expand-sa-node [#^::SANode node #^HashMap cache next-best state reward-to-state last-cutoff]
  (loop [new-results (if (= last-cutoff (cutoff node)) {}
                         (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
     (if (< (cutoff node) next-best)
         (PartialResult (stitch-results new-results state reward-to-state) (cutoff node))   
       (let [[entry neg-reward] (queues/pq-remove-min-with-cost! (queue node))
             b-s (:state entry), b-rts (:reward-to-state entry), b-ra (:remaining-actions entry), b-sa (:sanode entry)
             rec-next-best (max next-best (cutoff node))]
           (if (empty? b-ra)
               (let [eff (vary-meta (env/extract-effects b-s (:context node)) assoc :opt (:opt (meta b-s)))]
                 (swap! (:result-map-atom node) assoc-safe >= eff b-rts)
                 (recur (assoc-safe new-results >= eff b-rts)))
             (let [rec (expand-sa-node b-sa cache (- rec-next-best b-rts) b-s b-rts (- 0 neg-reward b-rts))]
               (when (> (:cutoff rec) Double/NEGATIVE_INFINITY) 
                 (queues/pq-replace! (queue node) entry (- 0 b-rts (:cutoff rec))))
               (doseq [[ss sr] (:result-map rec)]
                 (queues/pq-add! (queue node)
                   (SeqNodeEntry ss (when (next b-ra) (get-sa-node cache ss (second b-ra))) sr (next b-ra))
                   (- sr)))
               (recur new-results)))))))



(defn sahucs [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        init  (env/initial-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0 last-cutoff 0]
      (let [result (expand-sa-node root cache cutoff init 0.0 last-cutoff)]
;        (println "TOP" (:cutoff result) cutoff last-cutoff result)
        (cond (not (empty? (:result-map result)))
                (let [[k v] (util/first-maximal-element val (:result-map result))]
;                  (println k)
                  [(:opt (meta k)) v])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result) cutoff))))))

