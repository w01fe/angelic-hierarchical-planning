(ns exp.sahucs-dijkstra
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHTN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; TODO: pass incremental updates upwards. 
;; Difficulty: nodes with multiple ancestors.

(defprotocol HasCutoff (cutoff [x]))

(deftype PartialResult [result-map cutoff]
  HasCutoff (cutoff [] cutoff))

;(def *dummy-result* (PartialResult {} Double/NEGATIVE_INFINITY))


;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 

;; Know how to do cycclingSAnode.  How can we save results?
;; Every node keeps track of what it "loses", these become its queue ?


(deftype SANode [context action result-map-atom queue]
  HasCutoff (cutoff [] (- (second (queues/pq-peek-min queue)))))


(deftype CSANodeEntry [state sanode reward-to-state remaining-actions]
  Object
   (equals [y] (and (= state (:state y)) (= remaining-actions (:remaining-actions y))))
   (hashCode [] (unchecked-add (hash state) 
                               (unchecked-multiply 13 (hash remaining-actions)))))

(deftype CyclingSANode [context action result-map-atom queue cycle-level]
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

;; TODO: figure out how to avoid returning everything when only a few states are needed. (if needed)
 ; (< next-best (val %))
(defn expand-helper [node cache next-best last-cutoff result-fn]
  (loop [init-results (if (= last-cutoff (cutoff node)) {}
                          (util/filter-map #(<= (val %) last-cutoff) (:result-map @(:result-atom node))))]
    (if (< (cutoff node) next-best)
      (PartialResult init-results (cutoff node))
      (let [[best-child neg-reward] (queues/pq-remove-min-with-cost! (:queue node))
            next-best (max next-best (cutoff node))
            [new-states new-pairs] (result-fn best-child (- neg-reward) next-best)]
        (doseq [[n r] new-pairs] (queues/pq-add! (:queue node) n (- r)))
        (recur (merge init-results new-states))))))

(defn munge-results [result-map result-atom context state reward-to-state]
  (let [effect-map (util/map-keys #(env/extract-effects % context) result-map)]
    (swap! result-atom merge effect-map)
    (util/map-map (fn [[e r]] [(env/apply-effects state e) (+ r reward-to-state)]) effect-map)))

(declare  expand-seq-node)
(defn expand-sa-node [#^::SANode node #^HashMap cache next-best state reward-to-state last-cutoff]
  (expand-helper node cache next-best last-cutoff
    (fn [best-child reward next-best]
      (let [result (expand-seq-node best-child cache next-best)]
        [(munge-results (:result-map result) (:result-atom node) (:context node) state reward-to-state)
         [[best-child (:cutoff result)]]]))))

(defn expand-sa-node [#^::SANode node #^HashMap cache next-best state reward-to-state last-cutoff]
  (expand-helper node cache next-best last-cutoff
    (fn [best-child reward next-best]
      (let [result (expand-seq-node best-child cache next-best)]
        [(munge-results (:result-map result) (:result-atom node) (:context node) state reward-to-state)
         [[best-child (:cutoff result)]]]))))

(defn expand-seq-node [#^::SeqNode node #^HashMap cache next-best]
  (expand-helper node cache next-best (cutoff node)
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