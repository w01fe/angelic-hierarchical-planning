(ns exp.sahucs-nc
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap IdentityHashMap])
  )




;; This version is complete, optimal, and hopefully more efficient in the face of cycles.
;; (with some overhead).

;; Basic idea: all cycle-avoidance info should be reflected in what goes up the stack.  
;; Nothig should be recorded in nodes, other than leaving well enough alone.  
 ;; I.e., need to pass up failure set, temporarily treat children like they have modified
 ;; (i.e., artificially low) reward threshold in making decisions and computing upward values
 ;; but without actually changing anything.  
 ;; Must also pass up real cutoff 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unchanged from sahucs.clj

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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 

;; Here, it also stores the min depth (0+) of any node participating in a cycle,
;; (or nil, if none), and in this case cutoff may be artificially low. 
;; Also returns a separate bad-result-map for results that cannot be cached.

(deftype PartialResult [result-map cutoff min-cycle-depth bad-result-map])


(deftype SANode [context action result-map-atom queue])

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

; Only changes from sahucs.clj are in expand-sa-node.

(declare get-sa-node)
(defn get-sanode-entry [cache state reward-to-state actions]
  (make-sanode-entry state 
   (when (seq actions) (get-sa-node cache state (first actions)))
   reward-to-state actions))

(defn get-sa-node [#^HashMap cache s a]
  "Create a new sa-node, or returned the cached copy if it exists."
  (let [context (env/precondition-context a s)]
    (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
      (let [s     (env/get-logger s)
            prim? (env/primitive? a)
            [ss r] (when-let [x (and prim? (env/applicable? a s) (env/successor a s))] x)] ;pun        
        (SANode context a 
          (atom (if ss {(extract-effect ss context [a]) r} {})) 
          (make-queue (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
                        [(get-sanode-entry cache s 0.0 ref) 0.0])))))))


;; May return states better than next-best, but these will be held at the parent.
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff
                      #^IdentityHashMap stack-node-depths depth]
  (assert (not (.containsKey stack-node-depths node)))
  (.put stack-node-depths node depth)
  (loop [new-results (if (= last-cutoff (cutoff node)) {}
                         (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))
         min-cycle-depth 10000000000000
         bad-kids nil ; list of entries involved in cycles that need to be fixed before exit
         bad-results {}] 
     (if (< (cutoff node) next-best)
         (let [cut (cutoff node)] ; Cutoff before fixing cycling children.
           (.remove stack-node-depths node)
           (doseq [entry bad-kids] 
             (queues/g-pq-replace! (:queue node) entry 
               (- 0 (:reward-to-state entry) (if-let [n  (:sanode entry)] (cutoff n) 0))))
           (PartialResult (stitch-effect-map new-results state reward-to-state) cut min-cycle-depth
                          (stitch-effect-map bad-results state reward-to-state)))   
       (let [[entry neg-reward] (queues/g-pq-remove-min-with-cost! (:queue node))
             b-s (:state entry), b-rts (:reward-to-state entry), 
             b-ra (:remaining-actions entry), b-sa (:sanode entry),
             rec-next-best (- (max next-best (cutoff node)) b-rts)]
           (if (empty? b-ra)
               (let [eff (extract-effect b-s (:context node) (:opt (meta b-s)))]
                 (if bad-kids
                     (recur new-results min-cycle-depth (cons entry bad-kids)
                            (assoc-safe bad-results >= eff b-rts))
                   (do (swap! (:result-map-atom node) assoc-safe >= eff b-rts)
                       (recur (assoc-safe new-results >= eff b-rts) min-cycle-depth bad-kids bad-results))))
             (let [rec  (if-let [stack-depth (.get stack-node-depths b-sa)]
                            (PartialResult {} (- neg-reward) stack-depth {})
                          (expand-sa-node b-sa cache rec-next-best b-s b-rts (- 0 neg-reward b-rts)
                                          stack-node-depths (inc depth)))
                   inside-cycle? (< (:min-cycle-depth rec) depth)]
               (doseq [[ss sr] (:result-map rec)]
                 (queues/g-pq-add! (:queue node) (get-sanode-entry cache ss sr (next b-ra)) (- sr)))
               (when (or inside-cycle? (> (:cutoff rec) Double/NEGATIVE_INFINITY)) 
                 (queues/g-pq-replace! (:queue node) entry (- 0 b-rts (:cutoff rec))))
               (if inside-cycle?
                   (recur new-results (min min-cycle-depth (:min-cycle-depth rec)) (cons entry bad-kids) bad-results)
                 (recur new-results min-cycle-depth bad-kids bad-results))))))))

;; ALMOST: except suboptimal states may get cached at higher levels too.
;; Such bad states cannot be cached.  
;;  (DUH)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Only change from sahucs.clj: adding empty identity map, depth params to call.

(defn sahucs-nc [henv]
  (let [e     (hierarchy/env henv)
        cache (HashMap.)
        init  (env/initial-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0 last-cutoff 0]
      (let [result (expand-sa-node root cache cutoff init 0.0 last-cutoff (IdentityHashMap.) 0)]
        (cond (not (empty? (:result-map result)))
                (let [[k v] (util/first-maximal-element val (:result-map result))]
                  [(:opt (meta k)) v])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result) cutoff))))))






