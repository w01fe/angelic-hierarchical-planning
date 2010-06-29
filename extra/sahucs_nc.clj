(ns exp.sahucs-nc
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util [queues :as queues] [debug-repl :as dr]]
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
;; rec-context is just a context, to be passed back into the next recursive call so we can pick up where we left off.
(deftype PartialResult [result-map cutoff min-cycle-depth rec-context])

(deftype SANode [context action result-vec-and-map-atom queue])



;; Represents an action sequence from a state, with sanode representing the first action
; in remaining-actions. (or nil, if remaining-actions is empty.)
(deftype SANodeEntry [state sanode reward-to-state remaining-actions min-cycle-depth hash-code rec-context-atom] :as this
  Object
  (equals [y] (or (identical? this y) 
                  (and (= state (:state y)) (= remaining-actions (:remaining-actions y)))))
  (hashCode [] hash-code))

(defn make-sanode-entry [state sanode reward-to-state remaining-actions min-cycle-depth]
  (SANodeEntry state sanode reward-to-state remaining-actions min-cycle-depth
               (unchecked-add (int (hash state)) 
                              (unchecked-multiply (int 13) (int (hash remaining-actions))))
               (atom 0)))

(defn change-depth [entry new-cycle-depth]
  (SANodeEntry (:state entry) (:sanode entry) (:reward-to-state entry) (:remaining-actions entry)
               new-cycle-depth (:hash-code entry) (:rec-context-atom entry)))

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
                (atom (if ss (let [e (extract-effect ss context [a])] [[[e r]] {e r}]) [[] {}])) 
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
;        _ (println reward-cycle-depth cycle-depth)
        final-cycle-depth (min cycle-depth reward-cycle-depth)]
    (cond (= final-cycle-depth *infinite-depth*) :clean
          (= cycle-depth       *infinite-depth*) :dirtied
          :else                                  :still-dirty)))

(defn final-cycle-depth [reward cycle-depth cutoff-depth-map]
  (let [[_ reward-cycle-depth] (first (subseq cutoff-depth-map > reward))]
    (min cycle-depth reward-cycle-depth)))

(defn extend-cutoff-depth-map [cdm cutoff depth node-depth]
;  (println cdm cutoff depth)
  (let [[g-cutoff g-depth] (first (subseq cdm >= cutoff))]
    (if (< depth (min node-depth  g-depth)) (assoc cdm cutoff depth) cdm)))

(defn spos [s]  (try  (map #(env/get-var s %) '[[atx] [aty]]) (catch Exception e)))

;; May return states better than next-best, but these will be held at the parent.

;; Can't use last-cutoff as threshold for catchup because of cutoff duplicity.
(defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-context
                      #^IdentityHashMap stack-node-depths depth]
  (assert (not (.containsKey stack-node-depths node)))
 ; (println (apply str (repeat depth \ )) "Entering " (env/action-name (:action node)) (map #(env/get-var state %) '[[atx] [aty]]) "at depth" depth ", " (count (first @(:result-vec-and-map-atom node))) ", " (cutoff (:queue node)) next-best last-context reward-to-state)
;  (println (apply str (repeat depth \ )) "States on queue are: " (util/map-map (fn [[k v]] [[(spos (:state k)) (map env/action-name (:remaining-actions k))] (- v)]) (into {} (filter #(< (second %) Double/POSITIVE_INFINITY) (queues/pq-peek-pairs (:queue node))))))  
  (.put stack-node-depths node depth)
  (let [good-queue (:queue node)
        init-cutoff (cutoff good-queue)
        bad-queue  (queues/make-graph-search-pq)
        both-queue (queues/make-union-pq good-queue bad-queue)
        catchup    (into {} (drop last-context (first @(:result-vec-and-map-atom node))))
                                        ; (util/filter-map #(<= (val %) last-cutoff) @(:result-map-atom node))
                  ;  #_ (if (= last-cutoff (cutoff good-queue)) {}  ;; TODO: fix !?
        ;(util/filter-map #(<= (val %) last-cutoff) @(:result-map-atom node)))
        ]
    (loop [new-results      {}
           cutoff-depth-map (sorted-map Double/POSITIVE_INFINITY *infinite-depth*) 
           good-roots       nil]   ; jumping off points for unsavable computations.
      (if (< (cutoff both-queue) next-best)  ; Done
        (let [cut (cutoff both-queue) ; Cutoff before fixing cycling children.
              {:keys [clean dirtied still-dirty]} 
                (util/group-by (fn [[s r]] 
                                 (let [mcd (:min-cycle-depth (:entry (meta s)))]
                                   (assert (or (< mcd depth) (= mcd *infinite-depth*)))
                                   (classify-result-type r mcd cutoff-depth-map)))
                          new-results)]
          
          (swap! (:result-vec-and-map-atom node)
                 (partial reduce (fn [[ve m :as p] [k v :as p2]]
                                   (if-let [ov (get m k)]
                                     (do (assert (>= ov v))
                                         p)                                    
                                     [(conj ve p2) (assoc m k v)])))
                 clean)

;          (println (apply str (repeat depth \ )) (count clean) (count dirtied) (count still-dirty))
;          (when (= (first (env/action-name (:action node))) 'nav)
;            (let [[_ dx dy] (env/action-name (:action node))]
;              (doseq [[ss sr] (stitch-effect-map clean state 0 #_ reward-to-state)]
;                (println ss sr clean new-results (env/action-name (:action node)))
;                (let [[sx sy] (map #(env/get-var state %) '[[atx] [aty]])]
;                  (when-not (= (- sr) (+ (util/abs (- sx dx)) (util/abs (- sy dy))))
;                     (println "ERROR" [sx sy] [dx dy] sr (:min-cycle-depth (:entry (meta ss))) reward-to-state) #_ (dr/debug-repl))))))
          
          (doseq [entry (concat good-roots (map #(:entry (meta (key %))) dirtied))] 
            (assert (util/xor (not (:sanode entry)) (:cutoff (meta entry))))
            (assert (= (:min-cycle-depth entry) *infinite-depth*))
            (util/assert-is (<= (or (:cutoff (meta entry)) (:reward-to-state entry)) init-cutoff) "Bad cutoff %s %s" (:cutoff (meta entry)) (:reward-to-state entry))
            (queues/g-pq-replace! good-queue entry 
              (- (or (:cutoff (meta entry)) (:reward-to-state entry))))) ;(if-let [n  (:sanode entry)] (cutoff (:queue n)) 0)
          (.remove stack-node-depths node) ;; TODO: catchup!! 

       ;   (println (apply str (repeat depth \ )) "Returning from" (env/action-name (:action node)) (map #(env/get-var state %) '[[atx] [aty]]) "With cutoffs" cut (cutoff good-queue) ", ns"  (util/map-keys spos (stitch-effect-map catchup state reward-to-state) ) (count catchup) (count new-results))   
          (assert (<= (cutoff good-queue) init-cutoff))
          
          (PartialResult (stitch-effect-map 
                           (into {} (map (fn [[s r]] [(vary-meta s assoc :cycle-depth 
                                                        (final-cycle-depth r (or (:cycle-depth (:entry (meta s))) 
                                                                                 *infinite-depth*) cutoff-depth-map))
                                                      r])
                                         (concat new-results catchup)))
                           state reward-to-state) 
                         cut (val (first cutoff-depth-map)) (count (first @(:result-vec-and-map-atom node)))))   
        (let [[entry neg-reward] (queues/pq-remove-min-with-cost! both-queue)
              b-s (:state entry), b-rts (:reward-to-state entry), 
              b-ra (:remaining-actions entry), b-sa (:sanode entry), b-cd (:min-cycle-depth entry)
              rec-next-best (- (max next-best (cutoff both-queue)) b-rts)]
          (if (empty? b-ra)
              (do  ;(println (apply str (repeat depth \ )) "! found state" (map #(env/get-var b-s %) '[[atx] [aty]]) "for" (env/action-name (:action node)) "form" (map #(env/get-var state %) '[[atx] [aty]]) "with reward" b-rts "mcd" (:min-cycle-depth entry))
                (recur (assoc-safe new-results >=
                                  (vary-meta (extract-effect b-s (:context node) (:opt (meta b-s))) assoc :entry entry) b-rts)
                      cutoff-depth-map good-roots))
            (let [[rec rcut] (if-let [stack-depth (.get stack-node-depths b-sa)]
                            (do ;(println "Stack hit on" (env/action-name (:action b-sa)) (map #(env/get-var b-s %) '[[atx] [aty]])) 
                                [(PartialResult {} Double/NEGATIVE_INFINITY stack-depth @(:rec-context-atom entry)) (- neg-reward)])
                            [(expand-sa-node b-sa cache rec-next-best b-s b-rts @(:rec-context-atom entry)
                                              stack-node-depths (inc depth)) (+ (cutoff (:queue b-sa)) b-rts)])
;                  _                   (println (apply str (repeat depth \ )) "Got " b-cd (:min-cycle-depth rec) (util/map-keys (juxt spos (comp :cycle-depth meta)) (:result-map rec)))
                  rec-mcd (if (< (:min-cycle-depth rec) depth) (:min-cycle-depth rec) *infinite-depth*)
                  cd      (min b-cd rec-mcd)
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
              (assert (or (< b-cd depth) (= b-cd *infinite-depth*)))
              (assert (or (< cd depth) (= cd *infinite-depth*)))
;              (println (apply str (repeat depth \ )) (count good-nodes) (count nbn) (count dbn) (count sbn))
              (util/assert-is (<=  (+ b-rts (:cutoff rec)) (- neg-reward)) "%s %s %s" neg-reward b-rts (cutoff (:queue b-sa)))
              (reset! (:rec-context-atom entry) (:rec-context rec))
              (doseq [n good-nodes]      
                (when (> (:reward-to-state n) (min init-cutoff (- neg-reward)))
                  (util/assert-is (queues/g-pq-priority good-queue n) "%s %s %s %s %s %s" (:reward-to-state n) init-cutoff (- neg-reward)  (seq (spos state)) (str (seq (spos (:state n)))) (env/action-name (:action node)))
                  (assert (>= (queues/g-pq-priority good-queue n) (:reward-to-state n))))
                (queues/g-pq-add! good-queue n (- (:reward-to-state n))))
              (doseq [n (concat nbn sbn)] 
                (queues/g-pq-add! bad-queue  n (- (:reward-to-state n))))
              (when (> (:cutoff rec) Double/NEGATIVE_INFINITY)
                (when (>= cd depth) (assert (<= (+ b-rts (:cutoff rec)) (min init-cutoff (- neg-reward)))))
                (queues/g-pq-replace! (if (< cd depth) bad-queue good-queue) 
                                      (change-depth entry cd) ; ???
                                      (- 0 b-rts (:cutoff rec))))
              (recur new-results
                     (extend-cutoff-depth-map cutoff-depth-map (:cutoff rec) cd depth)
                     (concat (when (and (>= b-cd depth) (< cd depth)) 
;                               (util/assert-is (<=  (+ b-rts (:cutoff rec))  rcut (- neg-reward)) "%s %s %s ; %s %s %s" (cutoff (:queue b-sa)) b-rts (:cutoff rec) b-cd depth cd)
                               [(vary-meta entry assoc :cutoff (min rcut (- neg-reward)))]) ;; sometimes bad becomes good becomes bad.
                             (doall (for [n sbn] (queues/g-pq-remove! good-queue n)))
                             good-roots)))))))))

;; // TODO: now problem is that depths are actually relative.  good nodes should ahve no cycle depth.a
;; Think hard about how this works in, e.g., navigation.

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
        init  (env/initial-logging-state e)
        root  (get-sa-node cache init (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (loop [cutoff 0 last-cutoff 0]
;        (println "\ncutoff" cutoff "\n")
      (let [result (expand-sa-node root cache cutoff init 0.0 0 (IdentityHashMap.) 0)]
        (cond (not (empty? (:result-map result)))
                (let [[k v] (util/first-maximal-element val (:result-map result))]
                  [(:opt (meta k)) v])
              (> (:cutoff result) Double/NEGATIVE_INFINITY)
                (recur (:cutoff result) cutoff))))))


; still fails on 
; (sahucs-nc (simple-taxi-hierarchy (make-random-taxi-env 7 7 2 8)))



; (first (filter #(let [h (simple-taxi-hierarchy (make-random-taxi-env 2 3 2 %)) ] (println %) (not (= (prln  (second (sahtn-dijkstra h))) (second (exp.sahucs-nc/sahucs-nc h))))) (map (fn [x y] x) (range 100) (iterate inc 0))))
