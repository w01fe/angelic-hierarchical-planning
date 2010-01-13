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
(defprotocol HasQueue (queue [x]))

(deftype PartialResult [result-map cutoff]
  HasCutoff (cutoff [] cutoff))


;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 


(deftype SANode [context action result-map-atom queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue))))
  HasQueue  (queue [] queue))

(deftype SeqNodeEntry [state sanode reward-to-state remaining-actions]
  Object
   (equals [y] (and (= state (:state y)) (= remaining-actions (:remaining-actions y))))
   (hashCode [] (unchecked-add (int (hash state)) 
                               (unchecked-multiply (int 13) (int (hash remaining-actions))))))

(deftype SeqNode [queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue))))
  HasQueue  (queue [] queue))


(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/pq-add! q :dummy Double/POSITIVE_INFINITY)
    (queues/pq-add-all! q initial-elements)
    q))

(defn merge-safe 
  "Merge maps m1 and m2.  If a key is in m1 and m2, the value for m1 will be retained.
   Moreover, we will assert that (pred m1-val m2-val)."
  [pred m1 m2]
  (merge-with (fn [x y] (assert (pred x y)) x) m1 m2))

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
          (make-queue
           (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
             [(SeqNode (make-queue [[(SeqNodeEntry s (when (seq ref) (get-sa-node cache s (first ref))) 0.0 ref) 0.0]])) 0.0])))))))


;; Result-fn returns 
(defn expand-helper [node cache next-best init-results result-fn]
  (if (< (cutoff node) next-best)
    (do ;#_ (println "done " (type node)  (cutoff node) init-results) 
        (PartialResult init-results (cutoff node)))
    (let [[best-child neg-reward] (queues/pq-remove-min-with-cost! (queue node))
          next-best (max next-best (cutoff node))
          [new-states adj-reward new-pairs] (result-fn best-child (- neg-reward) next-best)]
      (when (> adj-reward Double/NEGATIVE_INFINITY) (queues/pq-replace! (queue node) best-child (- adj-reward)))
      (doseq [[n r] new-pairs] (queues/pq-add! (queue node) n (- r)))
      (recur node cache next-best (merge init-results new-states) result-fn))))


(defn stitch-results [effect-map state reward-to-state]
  (util/map-map 
   (fn [[effects local-reward]]
     [(vary-meta (env/apply-effects state effects) assoc :opt (concat (:opt (meta state)) (:opt (meta effects))))
      (+ reward-to-state local-reward)]) 
   effect-map))

;; May return states better than next-best, but these will be held at the seq node.
(declare  expand-seq-node)
(defn expand-sa-node [#^::SANode node #^HashMap cache next-best state reward-to-state last-cutoff]
;  (util/timeout)
;  (println "SA" (env/action-name (:action node)) last-cutoff (cutoff node) next-best reward-to-state)
  (util/assert-is (= (type node) ::SANode))
  (expand-helper node cache next-best
    (if (= last-cutoff (cutoff node)) {}
        (stitch-results 
         (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node))
         state reward-to-state))
    (fn [best-child reward next-best]
      (let [result (expand-seq-node best-child cache next-best)
            effect-map (util/map-keys #(vary-meta (env/extract-effects % (:context node)) assoc :opt (:opt (meta %)))
                                      (:result-map result))]
;        (println "Got seq results " result reward-to-state)
        (swap! (:result-map-atom node) (partial merge-safe >=) effect-map)
        [(stitch-results effect-map state reward-to-state) (:cutoff result) nil]))))

;; Will never return anything worse than next-best.  
(defn expand-seq-node [#^::SeqNode node #^HashMap cache next-best]
;  (println "Seq")
  (util/assert-is (= (type node) ::SeqNode))
  (expand-helper node cache next-best {}
    (fn [entry reward next-best]
      (let [{:keys [state reward-to-state remaining-actions sanode]} entry]
;        (println "ACTIONS " (map env/action-name remaining-actions))
        (if (empty? remaining-actions)
            [{state reward-to-state} Double/NEGATIVE_INFINITY nil]
          (let [result (expand-sa-node sanode cache (- next-best reward-to-state) state 
                                       reward-to-state (- reward reward-to-state))]
;            (println "SEQ" (:result-map result))
            [{} (+ reward-to-state (:cutoff result))             
              (for [[s r] (:result-map result)]
                [(SeqNodeEntry s (when (next remaining-actions) (get-sa-node cache s (second remaining-actions))) 
                               r (next remaining-actions)) 
                 r])]))))))


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

