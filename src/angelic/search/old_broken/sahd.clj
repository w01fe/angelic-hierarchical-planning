(ns angelic.sahd
  (:require [angelic.util :as util]
            [angelic.env :as env] 
            [angelic.hierarchy :as hierarchy]))

;; What happens in SAHA?
 ; Initially, get entire structure.
 ; Then, no AnyState, hence at most one result per. 
 ; Subproblems should be closed.  

(def any-state :AnyState)

(defmulti semiring-0 (fn [x] x))
(defmulti semiring-+ (fn [t x y] t))


(def additive-semiring ::additive-semiring)
(defmethod semiring-0 ::plus )

; Extra data should be a ring.
; ;Sort of ... need lists for combine-or, combine-and
 ; ; Or just pass in functions.
;; Anwyay, need way to *create*, get *0-element*, combine "or", combine "seq".  
 ; optimsitic bound, completed? is required, everything else is optional.
(defprotocol PartialSolution
  (solution-or-nil [ps])
  (combine-or [ps])
  (combine-seq [ps]))

; ;What kind of state would we really like to keep here?  
;Note it's going to be expensive to keep state, unless it
 ; Can share ordering with optimistic cost
 ; Supports "subtraction" as well.   
; Then there are things that are hybrids, like "min # of children expanded to increase cost."
; This is min at Seq, + among optimal at AND
; Fn should take queue, old child, new children, enqueue them and do its thing?

; Open: new states must flow upward, as well as new bound.
; Closed: only bounds flow up.  No notion of "goal".  
;  Is-solved? is a goal. ? 

;; Why do we need this distinction? As soon as we have 

(defprotocol Subproblem
  (name          [sp])  
  (current-ps    [sp])
;  (register-parent-context [sp context]) ; Register caller, for strictly new SPs only.
  (refine [sp stopping-condition]) ; Returns list of new subproblems?  Can include things like primitive required...
  (outcome-map [sp stopping-condition])
  )

;; Instantiated from HLA ? 
;; In context, we always have exactly one goal state? 
  ; Keeps a stopping condition.  May also house, e.g., irrelevant vars.
  ; 
(defprotocol SubproblemChild
  (output-state [sp])  
  (current-ps    [sp])
  (refine [sp reward-threshold])
  )

;; Should pass in optimistic/pessimistic fuctions  ? 
  ; (Need a way to make uninformed by exiting to AnyState immediately).

(deftype OrSubproblem [name child-queue] :as this 
  Subproblem
  (name [] name)
  (refine [sp reward-threshold]
    (loop [new-subproblems ???]
      (cond (queues/pq-empty? child-queue)
              new-subproblems
            (< (- (pq-peek-min-cost child-queue)) reward-threshold)
              (cons this new-subproblems)
            :else 
              (let [[m mc] (queues/pq-remove-min-with-cost! child-queue)]
                (let [nbc (if (queues/pq-empty? child-queue) Double/POSITIVE_INFINITY
                              (pq-peek-min-cost child-queue))]
                  (if ... is state ?)
                  )
                )
        
        ()
        )
      
      )          
          
          )
  )

(defn make-or-subproblem [options initial-state initial-children] 
  
  )

;; type of AND, chooses initial state
(deftype BinarySeqSubproblem [initial-state left right])

(defn make-binary-seq-subproblem [options initial-state left right])


(deftype PrimitiveSubproblem [initial-state primitive-action])

(defn make-primitive-subproblem [initial-state primitive-action])

; Each view on an, e.g., dijstra subproblem may want its own terminal set.
; May need some fancy indexing for this. 

; In particular, Subproblem should have partial goal, which recognizes all goals in any context.
;   Problem is keeping things straight; disallowing paths through one goal to another.  Suppose that's fine for now
;   Then, we use single open list, two closed lists - one per concrete goal, one global.
;   Or, we can just keep sub-closed-list at parent ? 
; Perhaps we skip this for now. ?


;; Want to still allow dijkstra, e.g.
;; Is this a subproblem? 
 ;; Or a -something-else- ? 
 ;; (is single-output-state a requirement or not?).
 
;; Perhaps: 3 layers.

; ??? - thing that actually does search
; ??? - thing that is cached
; ??? - thing that is contained within a search node.
; Actual search should be cached, clearly.


;(defprotocol )