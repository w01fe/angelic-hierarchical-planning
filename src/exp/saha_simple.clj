(ns exp.saha-simple
  (:require [edu.berkeley.ai.util :as util] [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;; Simplest possible SAHA
;; Assumes atomic-state angelic descriptions, always refines first 
;; action, no pessimistic descriptions.

; Node has fixed set of result states;
; what changes is cost estimate for these.
; Want to keep track of where best val for each came from.

; When we refine, pass in an outcome state and cutoff cost.
; Return value is simply new cost.

; Assume right-factored? Can we wtill do within-action DP ? 
; Trick: can do this as long as we always refine-first.
; Can keep similar format as before - action+rest-plan. 
; Question is how we factor this, or something...

; For now, easier if we assume all sharing is expressed by hierarchy ?
; Every state is "inside" a lower-level?
; Need a way to know which states are exact.
; I.e., may as well propagate both sides.  
; Do we do it as two separate maps, or a single map to interval? 
; Even if latter, still need to know if we have primitive solution for "wrap-up" phase.

; Two sets:
;   Final outcome states
;   Set of "leads" - primitive reachable state, partial first HLA, plus remaining HLAs. Right-factor: state-seq node, state-action node, 

; state-seq node is always just heuristics? No reason for this, really.

;; TODO: tiebreaking?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Helpers       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn assoc-safe [m pred k v]
  (if (contains? m k) 
    (do (assert (pred (get m k) v)) m)
    (assoc m k v)))


(defn extract-effect [state opt]
  (vary-meta (env/extract-effects state) assoc :opt opt))

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

;; TODO: handle state abstraction.
;; Whenever coming into SA-node, need to abstract.
;; Stitching *could* all happen at setup.  Then, where do solutions go ?
; They can go on outcome states, that's fine .. ?

; Two problems: 
  ; Querying states.  Now keeping LFS is fine, equality is correct.
  ;   But, how do we query for these?
  ;   (We may not know effect context .. ? . ? >?>?>??>)
  ;   -- we can cache outgoing-map, or something?
  ;   -- perhaps this is best.  
  ;   -- sanode can keep this translation layer itself?
  ;   -- or should refinement keep it for first-sa?
   ;   -- problem with this is final sa.  
   ;   -- can make this uniform, if that makes things easier. 
   
; finish-set should become solution-map.
; Also, must handle back-map.
; Finally, ideally should be able to catch more errors due to unexpectedly missing states.


(defprotocol Node
  (refine-state [n outcome-state cutoff]              
                "Refine and return nil..  May do nothing if state is solved,
                 but we didn't already know it.")
  (optimistic-reachable-set [n])
  (optimistic-reward [n state] "Return reward for state.")
  (state-solution    [n state] "Return sol for state, or nil if unsolved."))




(defn best-and-next-score [nodes score-fn]
  (assert (seq nodes))
  (let [[best next-best] (sort-by #(- (score-fn %)) nodes)]
    [best (if next-best (score-fn next-best) Double/NEGATIVE_INFINITY)]))

(defn do-refinement [parent-node child-node outcome-state cutoff context-reward next-best-reward pre-sol]
  (when-not (state-solution child-node outcome-state) 
    (refine-state child-node outcome-state (- (max cutoff next-best-reward) context-reward)))
  (let [new-reward (optimistic-reward child-node outcome-state)
        new-reward-in-context (+ new-reward context-reward)]
    (when-not (state-solution child-node outcome-state)
      (util/assert-is (< new-reward-in-context (max cutoff next-best-reward))))
    
    (swap! (:optimistic-val-atom parent-node) 
           assoc outcome-state (max new-reward-in-context next-best-reward))
    (when-let [sol (and (>= new-reward-in-context next-best-reward)
                        (state-solution child-node outcome-state))]
;      (println "Solved" outcome-state new-reward-in-context (optimistic-reward child-node outcome-state)
;               (if (:action parent-node) (env/action-name (:action parent-node))))
      (swap! (:solution-map-atom parent-node) assoc outcome-state (concat pre-sol sol)))))

; refinements is a lazy seq... we don't evaluate it when we first create the node.
; TODO: How does this compare to using state-rest version?  
(deftype SANode [state action refinements solution-map-atom optimistic-val-atom] :as this
  Node
  (refine-state         [outcome-state cutoff]
    (when-not refinements (util/assert-is nil "%s" [(env/action-name action) outcome-state @solution-map-atom @optimistic-val-atom state]))
 ;   (println "Refining sanode" (env/action-name action) "from" state "to" outcome-state (optimistic-reward this outcome-state) cutoff)
    (while (and (not (state-solution this outcome-state))
                (>=  (optimistic-reward this outcome-state) cutoff))
      (let [[best next-best-reward] (best-and-next-score refinements #(optimistic-reward % outcome-state))]
        (do-refinement this best outcome-state cutoff 0 next-best-reward []))))
  (optimistic-reachable-set [] (util/keyset @optimistic-val-atom))
  (optimistic-reward [outcome-state]
    (get @optimistic-val-atom outcome-state Double/NEGATIVE_INFINITY))
  (state-solution    [outcome-state]
    (get @solution-map-atom outcome-state)))

; Outcome-map maps from use's versions of outcome state to sanode's canonical ones.
(deftype SANodeWrapper [state sanode outcome-map]
  Node
  (refine-state [outcome-state cutoff]
   (refine-state sanode (util/safe-get outcome-map outcome-state) cutoff))
  (optimistic-reachable-set [] (util/keyset outcome-map))
  (optimistic-reward [outcome-state]
    (optimistic-reward sanode (util/safe-get outcome-map outcome-state)))
  (state-solution    [outcome-state]
    (state-solution sanode (util/safe-get outcome-map outcome-state))))

(declare make-ref-node)

(defn create-sa-node [cache s a ]
  (if (env/primitive? a)
    (if-let [[ss r] (when (env/applicable? a s) (env/successor a s))]
      (SANode s a nil (atom {ss [a]}) (atom {ss r}))
      (SANode s a nil (atom {}) (atom {})))
    (let [refs (hierarchy/immediate-refinements a s)
          [empty-refs ne-refs] (split-with empty? refs)]
      (SANode s a
              (for [ref ne-refs] (make-ref-node cache s ref))
              (atom (if (seq empty-refs) {s []} {}))
              (atom (if (seq empty-refs) (assoc (env/optimistic-map a s) s 0) (env/optimistic-map a s)))))))

(defn get-sa-node [#^HashMap cache s a]
  (let [context   (env/precondition-context a s)
        node      (util/cache-with cache [(env/action-name a) (env/extract-context s context)] 
                                   (create-sa-node cache (env/get-logger s context) a))]
    (SANodeWrapper s node
       (into {}
         (for [ss (optimistic-reachable-set node)]
           [(env/apply-effects s (env/extract-effects ss)) ss])))))

(deftype RefNode [state first-sa successors solution-map-atom optimistic-val-atom] :as this
  Node
  (refine-state  [outcome-state cutoff]
    (while (and (not (state-solution this outcome-state))
                (>=  (optimistic-reward this outcome-state) cutoff))                 
      (let [[best next-best-reward] (best-and-next-score successors 
                                      #(+ (optimistic-reward first-sa (:state %))
                                          (optimistic-reward % outcome-state)))
            best-state       (:state best)]
        (if-let [sol (state-solution first-sa best-state)] 
          (do-refinement this best outcome-state cutoff (optimistic-reward first-sa best-state) next-best-reward sol)
          (do-refinement this first-sa best-state cutoff (optimistic-reward best outcome-state) next-best-reward [])))))
  (optimistic-reachable-set [] (util/keyset @optimistic-val-atom))
  (optimistic-reward [outcome-state]
    (get @optimistic-val-atom outcome-state Double/NEGATIVE_INFINITY))
  (state-solution    [outcome-state]
    (get @solution-map-atom outcome-state)))

(defn make-ref-node [#^HashMap cache s ref]
  (assert (seq ref))
  (let [[first-action & more-actions] ref
        first-sa (get-sa-node cache s first-action)]
    (if (empty? more-actions) first-sa
      (let [first-outcomes (optimistic-reachable-set first-sa)
            successors (for [s first-outcomes] (make-ref-node cache s more-actions))
            full-val   (apply merge-with max
                         (for [succ successors :let [sr (optimistic-reward first-sa (:state succ))]
                               ss   (optimistic-reachable-set succ)]
                           {ss (+ sr (optimistic-reward succ ss))}))]
        (RefNode s first-sa successors (atom {}) (atom full-val))))))

(comment (into {} (for [succ    successors
                :let    [sr (first-val (:state succ))]
                [fs fr] (optimistic-valuation succ)
                :when   (== (+ sr fr) (full-val fs))]
            [fs :dummy])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Top-level    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn saha-simple [henv]
  (let [e     (hierarchy/env henv)
        root  (get-sa-node (HashMap.)
                (env/initial-logging-state e)
                (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]))]
    (when-let [goals (seq (optimistic-reachable-set root))]
      (let [goal (util/safe-singleton goals)]
        (refine-state root goal Double/NEGATIVE_INFINITY)
        (let [rew (optimistic-reward root goal)]
          (when (> rew Double/NEGATIVE_INFINITY)
            [(util/make-safe (state-solution root goal)) rew]))))))



(comment ; old stuff from sahucs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Core Algorithm  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (declare get-sa-node)

  (defn get-sa-node [#^HashMap cache s a]
    "Create a new sa-node, or returned the cached copy if it exists."
    (let [context (env/precondition-context a s)]
      (util/cache-with cache [(env/action-name a) (env/extract-context s context)]
                       (let [s     (env/get-logger s context)
                             prim? (env/primitive? a)
                             [ss r] (when-let [x (and prim? (env/applicable? a s) (env/successor a s))] x)] ;pun        
                         (SANode  a 
                                  (atom (if ss {(extract-effect ss  [a]) r} {})) 
                                  (make-queue (for [ref (when-not prim? (hierarchy/immediate-refinements a s))]
                                                [(get-sanode-entry cache s 0.0 ref) 0.0])))))))


;; May return states better than next-best, but these will be held at the parent.
  (defn expand-sa-node [node #^HashMap cache next-best state reward-to-state last-cutoff]
    (loop [new-results (if (= last-cutoff (cutoff node)) {}
                           (util/filter-map #(<= (val %) last-cutoff)  @(:result-map-atom node)))]
      (if (< (cutoff node) next-best)
        (PartialResult (stitch-effect-map new-results state reward-to-state) (cutoff node))   
        (let [[entry neg-reward] (queues/g-pq-peek-min (:queue node))
              b-s (:state entry), b-rts (:reward-to-state entry), 
              b-ra (:remaining-actions entry), b-sa (:sanode entry)
              rec-next-best (- (max next-best (cutoff node)) b-rts)]
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





)