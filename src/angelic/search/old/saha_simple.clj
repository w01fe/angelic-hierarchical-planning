(ns angelic.saha-simple
  (:require [angelic.util :as util] [angelic.util.queues :as queues]
            [angelic [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;; Simplest possible SAHA
;; Assumes atomic-state angelic descriptions, always refines first 
;; action, no pessimistic descriptions.

;; NOTE: this is not properly lazy about something or other.  We can do 3x better, see hierarhcical_search.explicit.

; Node has fixed set of result states;
; what changes is cost estimate for these.
; Want to keep track of where best val for each came from.

; When we refine, pass in an outcome state and cutoff cost.

; For now, easier if we assume all sharing is expressed by hierarchy ?
 ; (don't bother to factor)

;; Note: sorting is stable, so tiebreaking is not really needed ? 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Data Structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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
              (atom (if (seq empty-refs) (assoc (angelic/optimistic-map a s) s 0) (angelic/optimistic-map a s)))))))

(defn get-sa-node [^HashMap cache s a]
  (let [context   (env/precondition-context a s)
        node      (util/cache-with cache [(env/action-name a) (state/extract-context s context)] 
                                   (create-sa-node cache (env/get-logger s context) a))]
    (SANodeWrapper s node
       (into {}
         (for [ss (optimistic-reachable-set node)]
           [(state/apply-effects s (env/extract-effects ss)) ss])))))

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

(defn make-ref-node [^HashMap cache s ref]
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
                (hierarchy/hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)]))]
    (when-let [goals (seq (optimistic-reachable-set root))]
      (let [goal (util/safe-singleton goals)]
        (refine-state root goal Double/NEGATIVE_INFINITY)
        (let [rew (optimistic-reward root goal)]
          (when (> rew Double/NEGATIVE_INFINITY)
            [(util/make-safe (state-solution root goal)) rew]))))))


