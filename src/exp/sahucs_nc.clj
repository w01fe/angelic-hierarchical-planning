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

(defn merge-safe [pred & maps]
  (merge-with (fn [x y] (assert (pred x y)) x)))


(defn extract-effect [state context opt]
  (vary-meta (env/extract-effects state context) assoc :opt opt))

(defn stitch-effect-map [effect-map state reward-to-state]
  (util/map-map1 
   (fn [[effects local-reward]]
     [(vary-meta (env/apply-effects state effects) assoc 
                 :opt (concat (:opt (meta state)) (:opt (meta effects)))
                 :cycle-depth (:cycle-depth (meta effects)))
      (+ reward-to-state local-reward)]) 
   effect-map))


(defn cutoff [queue]
  (- (nth (queues/pq-peek-min queue) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A PartialResult stores a map from states to rewards, where a state is present
;; iff it has reward > cutoff. 

;; Here, it also stores the min depth (0+) of any node participating in a cycle,
;; (or nil, if none), and in this case cutoff may be artificially low. 
;; Also returns a separate bad-result-map for results that cannot be cached.

(deftype PartialResult [result-map cutoff min-cycle-depth])

(deftype SANode [context action result-map-atom queue])



;; Represents an action sequence from a state, with sanode representing the first action
; in remaining-actions. (or nil, if remaining-actions is empty.)
(deftype SANodeEntry [state sanode reward-to-state remaining-actions min-cycle-depth hash-code] :as this
  Object
  (equals [y] (or (identical? this y) 
                  (and (= state (:state y)) (= remaining-actions (:remaining-actions y)))))
  (hashCode [] hash-code))

(defn make-sanode-entry [state sanode reward-to-state remaining-actions min-cycle-depth]
  (SANodeEntry state sanode reward-to-state remaining-actions min-cycle-depth
               (unchecked-add (int (hash state)) 
                              (unchecked-multiply (int 13) (int (hash remaining-actions))))))

;(defn change-depth [entry new-cycle-depth]
;  (SANodeEntry (:state entry) (:sanode entry) (:reward-to-state entry) (:remaining-actions entry)
;               new-cycle-depth (:hash-code entry)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Algorithm  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Only changes from sahucs.clj are in expand-sa-node.

(def *infinite-depth* 1000000000000)

(declare get-sa-node)
(defn get-sanode-entry [cache state reward-to-state actions min-cycle-depth]
  (make-sanode-entry state 
   (when (seq actions) (get-sa-node cache state (first actions)))
   reward-to-state actions min-cycle-depth))

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
                        [(get-sanode-entry cache s 0.0 ref *infinite-depth*) 0.0])))))))

;; Three things need to be dealt with -- bad states, bad states, entries based on bad states, bad roots.

;; Simple union priority queue is not enough, since we may get duplicate states.
;; Not the end of the world, but we would like to solve properly.
; Shadowed priority queue might be right ??
; Issue: what if bad state is better than good one ?
;;  Yikes, this could create all sorts of problems, ala inconsistent heuristic.
 ;  Note you can only get bad states back from a bad child.
 ;  Thus, in this case even the "good" state will be returned as bad. 
 ; Two cases: good state added to queue in previous iteration --> 

;; Also, in domain with reversible actions, everything will be bad regardless (?)

 ;  Also, what happens when we revisit a node -- we redo all local work, recreate bad states, re-return them?

;; Also, think about simple dijkstra version, and what it loses (e.g., nothing for single-action, right-recursive,
 ;; top-level search.)

;; Also, can use retroactive tie-breaking to maximize the good. (cost threshold).  
;; This solves result-graphiness problem.
 ;; Still have entry-queue-issue.  
   ;; Here, a better bad should temporarily hide an identical good, but good must remain next time.
   ;; OTOH, a worse bad (than identical good/bad) should just be dropped.
  ;; (the order they are found should not matter)

;; IF we assume strictly positive-cost actions: then, good/bad state divide is just a cost threshold ? 
   ; No, it's an increasing mapping from reward to stack depth.
    ; (plus, individual state's stack depth must be taken into account.)

;; General rule: if any part of a computational result from a clean entry is dirty, entry must be saved.

;; State depths are recorded in :cycle-depth in metadata  - mandatory in return values.

;; TODO: watch out for zero reward ?

;; TODO::: FIX queue bs.

; three classes of states - clean, just dirty, already dirty
(defn classify-result-type [reward cycle-depth cutoff-depth-map]
  (let [[_ reward-cycle-depth] (first (subseq cutoff-depth-map > reward))
        final-cycle-depth (min cycle-depth reward-cycle-depth)]
    (cond (= final-cycle-depth *infinite-depth*) :clean
          (= cycle-depth       *infinite-depth*) :dirtied
          :else                                  :still-dirty)))

(defn final-cycle-depth [reward cycle-depth cutoff-depth-map]
  (let [[_ reward-cycle-depth] (first (subseq cutoff-depth-map > reward))]
    (min cycle-depth reward-cycle-depth)))

(defn extend-cutoff-depth-map [cdm cutoff depth]
  (let [[g-cutoff g-depth] (first (subseq (cdm >= cutoff)))]
    (if (< depth g-depth) (assoc cdm cutoff depth) cdm)))

;; May return states better than next-best, but these will be held at the parent.
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff
                      #^IdentityHashMap stack-node-depths depth]
  (assert (not (.containsKey stack-node-depths node)))
  (.put stack-node-depths node depth)
  (let [good-queue (:queue node)
        bad-queue  (queues/make-graph-stack-pq)
        both-queue (queues/make-union-pq good-queue bad-queue)
        catchup    (if (= last-cutoff (cutoff good-queue)) {}
                     (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
    (loop [new-results      {}
           cutoff-depth-map (sorted-map Double/POSITIVE_INFINITY *infinite-depth*) 
           good-roots       nil]   ; jumping off points for unsavable computations.
      (if (< (cutoff both-queue) next-best)  ; Done
        (let [cut (cutoff both-queue) ; Cutoff before fixing cycling children.
              {:keys [clean dirtied still-dirty]} 
                (util/group-by (fn [[s r]] (classify-result-type r (:cycle-depth (:entry (meta s))) cutoff-depth-map))
                          new-results)]
          (swap! (:result-map-atom node) (partial merge-safe >=) (into {} clean))
          (doseq [entry (concat good-roots (map #(:entry (meta (key %))) dirtied))] 
            (queues/g-pq-replace! good-queue entry 
              (- 0 (:reward-to-state entry) (if-let [n  (:sanode entry)] (cutoff (:queue n)) 0))))
          (.remove stack-node-depths node) ;; TODO: catchup!! 
          (PartialResult (stitch-effect-map 
                           (into {} (map (fn [[s r]] [(vary-meta s assoc :cycle-depth 
                                                        (final-cycle-depth r (or (:cycle-depth (:entry (meta s))) 
                                                                                 *infinite-depth*) cutoff-depth-map))
                                                      r])
                                         (concat new-results catchup)))
                           state reward-to-state) 
                         cut (val (first cutoff-depth-map))))   
        (let [[entry neg-reward] (queues/g-pq-remove-min-with-cost! (:queue node))
              b-s (:state entry), b-rts (:reward-to-state entry), 
              b-ra (:remaining-actions entry), b-sa (:sanode entry), b-cd (:min-cycle-depth entry)
              rec-next-best (- (max next-best (cutoff both-queue)) b-rts)]
          (if (empty? b-ra)
              (recur (assoc-safe new-results >=
                       (vary-meta (extract-effect b-s (:context node) (:opt (meta b-s))) assoc :entry entry) b-rts)
                     cutoff-depth-map good-roots)
            (let [rec (if-let [stack-depth (.get stack-node-depths b-sa)]
                           (PartialResult {} Double/NEGATIVE_INFINITY stack-depth)
                         (expand-sa-node b-sa cache rec-next-best b-s b-rts (- 0 neg-reward b-rts)
                                         stack-node-depths (inc depth)))
                  cd  (min b-cd (:min-cycle-depth rec))
                  result-nodes (for [[ss sr] (:result-map rec)
                                     :let [s-cd (min (:cycle-depth (meta ss)) b-cd)]]                                 
                                 (get-sanode-entry cache ss sr (next b-ra) (if (< s-cd depth) s-cd *infinite-depth*)))
                  [good-nodes bad-nodes] (split-with #(>= (:min-cycle-depth %) depth) result-nodes)
                  {:keys [nbn dbn sbn]}  (util/group-by
                                          (fn [node]
                                            (let [good-pri (queues/g-pq-priority good-queue node)]
                                              (cond (nil? good-pri)                          :nbn
                                                    (< (- good-pri) (:reward-to-state node)) :sbn
                                                    :else                                    :dbn)))
                                          bad-nodes)]
              (doseq [n good-nodes]       (queues/g-pq-add! good-queue n (- (:reward-to-state n))))
              (doseq [n (concat nbn sbn)] (queues/g-pq-add! bad-queue  n (- (:reward-to-state n))))
              (when (> (:cutoff rec) Double/NEGATIVE_INFINITY)
                (queues/g-pq-replace! (if (< cd depth) bad-queue good-queue) entry (- 0 b-rts (:cutoff rec))))
              (recur new-results
                     (extend-cutoff-depth-map cutoff-depth-map (:cutoff rec) cd)
                     (concat (when (and (>= b-cd depth) (< cd depth)) [entry])
                             (doall (for [n sbn] (queues/g-pq-remove! good-queue n)))
                             good-roots)))))))))

;; ALMOST: except suboptimal states may get cached at higher levels too.
;; Such bad states cannot be cached.  
;;   You also have to actually use them, and keep track of all successors and mark as bad too.
;;   Same rules apply for them to "become good".

;; Two sets of things happening, with children + states + cutoffs -- easy way to unify?
  ;; e.g., second queue? 

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






