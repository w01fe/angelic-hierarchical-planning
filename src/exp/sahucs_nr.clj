(ns exp.sahucs-nr
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHTN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version will loop forever on recursive hierarchies

;; TODO: pass incremental updates upwards. 
;; Difficulty: nodes with multiple ancestors.

(defprotocol HasCutoff (cutoff [x]))

(deftype PartialResult [result-map cutoff]
  HasCutoff (cutoff [] cutoff))

;(def *dummy-result* (PartialResult {} Double/NEGATIVE_INFINITY))


;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 


(deftype SANode [context action result-map-atom queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue)))))

(deftype SeqNodeEntry [state sanode reward-to-state remaining-actions]
  Object
   (equals [y] (and (= state (:state y)) (= remaining-actions (:remaining-actions y))))
   (hashCode [] (unchecked-add (hash state) 
                               (unchecked-multiply 13 (hash remaining-actions)))))

(deftype SeqNode [queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue)))))


(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/pq-add! q :dummy Double/POSITIVE_INFINITY)
    (queues/pq-add-all! q initial-elements)
    q))



(defn- get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
      (let [s     (env/get-logger s)
            prim? (env/primitive? a)]        
        (SANode context a 
          (atom (util/map-keys #(env/extract-effects % context) 
                          (into {} (and prim? (env/applicable? a s) (env/successor a s))))) 
          (make-queue
           (for [ref (when-not prim? (hierarchy/immediate-refinements s a))]
             [(SeqNode s (make-queue [[(SeqNodeEntry (get-sa-node cache s (first ref)) 0 (next ref)) 0]])) 0])))))))


;; Result-fn returns 
(defn expand-helper [node cache next-best init-results result-fn]
  (if (< (cutoff node) next-best)
      (PartialResult init-results (cutoff node))
    (let [[best-child neg-reward] (queues/pq-remove-min-with-cost! (:queue node))
          next-best (max next-best (cutoff node))
          [new-states new-pairs] (result-fn best-child (- neg-reward) next-best)]
      (doseq [[n r] new-pairs] (queues/pq-add! (:queue node) n (- r)))
      (recur node cache next-best (merge init-results new-states) result-fn))))

(declare  expand-seq-node)
(defn expand-sa-node [#^::SANode node #^HashMap cache next-best state reward-to-state last-cutoff]
  (expand-helper node cache next-best
    (if (= last-cutoff (cutoff node)) {}
        (util/filter-map #(<= (val %) last-cutoff) (:result-map @(:result-atom node))))
    (fn [best-child reward next-best]
      (let [result (expand-seq-node best-child cache next-best)
            effect-map (util/map-keys #(env/extract-effects % (:context node)) (:result-map result))]
        (swap! @(:result-atom node) merge effect-map)
        [(util/map-map (fn [[e r]] [(env/apply-effects state e) (+ r reward-to-state)]) effect-map) 
         [[best-child (:cutoff result)]]]))))

(defn expand-seq-node [#^::SeqNode node #^HashMap cache next-best]
  (expand-helper node cache next-best {}
    (fn [entry reward next-best]
      (let [rts (:reward-to-state entry)
            result (expand-sa-node (:sanode entry) cache (- next-best rts) (:state entry) rts (- reward rts))
            actions (:remaining-actions entry)]
        [(when (empty? actions) (:result-map result))
         (concat
          (when-not (= (:cutoff result) Double/NEGATIVE_INFINITY) 
            [[entry (:cutoff result)]])
          (when-not (empty? actions)
            (for [[s r] (:result-map result)]
              [(SeqNodeEntry (get-sa-node cache s (first actions)) r (next actions)) r ])))]))))


;; Must deal with no-children case in initial creation...

;    (loop [new-results ]
;      (if (< (cutoff node) next-best)
;        (PartialResult new-results (cutoff node))
;        (let [[best-child next-best-child] (sort-by #(- (cutoff %)) (:children node))
;              ]
;          (swap! (:result-atom node) 
;                 #(PartialResult (merge (:result-map %) (:result-map result))
;                                 (max   (cutoff result) (cutoff next-best-child))))
;          (recur (merge new-results (:result-map result))))))