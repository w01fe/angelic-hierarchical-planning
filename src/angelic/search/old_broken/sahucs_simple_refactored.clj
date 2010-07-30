(ns w01fe.sahdd
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [w01fe.env :as env] 
            [w01fe.hierarchy :as hierarchy])
  (:import  [java.util HashMap]))

; Here, there is no real Seq character.  No real choices.  
; Note: hard (impossible?) to unify down and up.
; Best: at least have common interface, shared parts, to simplify.

; Also fancier info going up, abstracted goals, etc.  

;; Also pass in antagonistic measure ? 

;; Should fix cost-order of subproblems.
 ;; I.e., right now, even if we have a given threshold, we return all states up to that.
 ;; Should return just first state, since it represents new alternative at higher level.
 ;; Ideally, this should just fall out of proper thinking.

; Question: what is general way to do this? 
; Note: to think of this as like SAHA, always refining a given outcome state.
;    Can think: always refining *abstracted* outcome state.
;    Note key difference: in SAHA we're doing bidi, in UCS we do forward dijkstra

; Also need goal-hiding, etc. ?

; Basic difference betwen top-down and bottom-up:
 ; top-down: give me updates since X
 ; bottom-up: give me updates as you get them, only of particular form. 
 ; For now, fix this, then extend. 


; We should still (unfortunately) never close open subproblems with cycles.  

;; For now, how do we pass states up?
  ; Store index / partial list in SubproblemEntry?
  ; Store cost and loop through?
  ; Keep queue, upwards pointers? 
  ;  Ideally, have single queue, "fingers" into it in each subproblem. 
  ;   Can almost do this with lazy seqs... ?!


(defn viable? [reward cutoff]
  (and (> reward Double/NEGATIVE_INFINITY)
       (>= reward cutoff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queues ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-queue-priority [reward]
  [(- reward)])

(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/g-pq-add! q :dummy (make-queue-priority Double/NEGATIVE_INFINITY))
    (doseq [[e r] initial-elements] (queues/pq-add! q e (make-queue-priority r)))
    q))

(defn empty-queue [queue]
  (queues/pq-remove-all! queue)
  (queues/g-pq-replace! queue :dummy (make-queue-priority Double/NEGATIVE_INFINITY)))

(defn queue-best-reward [queue]
  (- (first (nth (queues/g-pq-peek-min queue) 1))))

(defn queue-best-and-next-reward [queue]
  (let [[best bc] (queues/pq-remove-min-with-cost! queue)
        next-reward (queue-best-reward queue)]
    (queues/pq-replace! queue best bc)
    [best next-reward]))

(defn queue-cutoff [queue min-reward]
  (let [cutoff (double (queue-best-reward queue))]
    (when-not (viable? cutoff min-reward) cutoff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Outcome maps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn generalize-outcome-pair [[outcome-state reward] gen-state reward-to-gen-state]
  [(vary-meta (env/apply-effects gen-state (env/extract-effects outcome-state)) assoc 
              :opt (concat (:opt (meta gen-state)) (:opt (meta outcome-state))))
   (+ reward reward-to-gen-state)])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem 
  (sub-refine [sp min-reward] "Output is [result reward], reward >= min, or new threshold < min."))

(declare se-goal se-refine)

(defn pretty-state [s]
  (dissoc (env/as-map (or s {})) :const))

(deftype OpenSubproblem [name child-queue] :as this
  Subproblem
  (sub-refine           [min-reward]
    (util/print-debug 1 "\nRefining " (second  name) (first name) "with min-reward [" min-reward "]" "\n" (map #(vector (pretty-state (:initial-state (first %))) (map env/action-name (:remaining-actions (first %))) (next %)) (queues/pq-peek-pairs child-queue)))
    (loop []                        
;      (println (queue-best-reward child-queue))
      (or (queue-cutoff child-queue min-reward) 
          (let [[best next-best-reward] (queue-best-and-next-reward child-queue)]
            (if-let [g (se-goal best)]
              (do (queues/pq-remove! child-queue best) g)
              (let [[[_ new-rew] & new-items] (se-refine best (max min-reward next-best-reward))]
                (queues/pq-replace! child-queue best (make-queue-priority new-rew))
                (doseq [[ni nr] new-items] (queues/pq-add! child-queue ni (make-queue-priority nr)))
                (recur))))))))

(declare make-subproblem-entry)

(defn make-subproblem-entries [action state]
  (if (env/primitive? action)
      (when-let [p (and (env/applicable? action state) (env/successor action state))]
        [(make-subproblem-entry p nil)])
    (for [ref (hierarchy/immediate-refinements action state)]
      (make-subproblem-entry [state 0] ref))))

(defn make-open-subproblem [name state action]
  (OpenSubproblem name (make-queue (make-subproblem-entries action state))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Shared Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An interface to allow subproblems to be shared, while pretending they have single consumer.
;;; Not thread safe. 

(deftype SharedSubproblemCache [subproblem result-vec-atom next-reward-atom]
  Subproblem
  (sub-refine [min-reward]
    (util/print-debug 2 "SSPC" min-reward (Thread/sleep 10))               
    (assert (viable? @next-reward-atom min-reward))
    (let [result (sub-refine subproblem min-reward)]
      (if (number? result)
          (reset! next-reward-atom result)
        (do (swap! result-vec-atom conj result)
            (reset! next-reward-atom (nth result 1))))
      result)))

(defn make-shared-subproblem-cache [subproblem]
  (SharedSubproblemCache subproblem (atom []) (atom Double/POSITIVE_INFINITY)))


(deftype SharedSubproblem [cache index-atom]
  Subproblem
  (sub-refine [min-reward]
   (let [{:keys [subproblem result-vec-atom next-reward-atom]} cache]
     (util/print-debug 2 "SSP" min-reward @next-reward-atom (Thread/sleep 10)) 
    (if (< @index-atom (count @result-vec-atom))
          (let [[_ rew :as result] (nth @result-vec-atom @index-atom)]
            (if (>= rew min-reward)
                (do (swap! index-atom inc) result)
              rew))
        (if (viable? @next-reward-atom min-reward)
            (do (sub-refine cache min-reward)
                (recur min-reward))
          @next-reward-atom)))))

(defn make-shared-subproblem [cache]
  (SharedSubproblem cache (atom 0)))


(def #^HashMap *subproblem-cache*)

(defmacro get-subproblem-instance [name & body]
  `(let [name# ~name
         inst# (find *subproblem-cache* name#)]
     (if inst# (nth inst# 1)
       (let [x# (do ~@body)]
;         (println "Created fresh.")
         (.put *subproblem-cache* name# x#)
         x#))))

(defn get-open-subproblem-instance [state action]
;  (println "\nGetting subproblem" (env/as-map state) (env/action-name action) "\n")
  (let [context   (env/precondition-context action state)
        name     [(env/extract-context state context) (env/action-name action)]]
    (make-shared-subproblem 
     (get-subproblem-instance name 
       (make-shared-subproblem-cache
        (make-open-subproblem name (env/get-logger state context) action))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Entries ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol PSubproblemEntry
  (se-goal       [se])
  (se-refine     [se new-threshold] "Returns list of new queue entries; first is always self."))

(deftype SubproblemEntry [hash-code initial-state reward child-subproblem remaining-actions] :as this
  Object
  (equals [y] (or (identical? this y) 
                  (and (identical? child-subproblem (:child-subproblem y)) 
                       (= remaining-actions (:remaining-actions y)))))
  (hashCode [] hash-code)
  PSubproblemEntry
  (se-goal       [] (when (nil? child-subproblem) [initial-state reward]))
  (se-refine     [min-reward]
    (util/print-debug 2 "SE-R" min-reward (Thread/sleep 10)) 
    (assert child-subproblem)
    (let [result (sub-refine child-subproblem (- min-reward reward))]
      (if (number? result) 
          [[this (+ result reward)]]
        [[this (nth result 1)] 
         (make-subproblem-entry (generalize-outcome-pair result initial-state reward) remaining-actions)]))))

(defn make-subproblem-entry [[initial-state reward] remaining-actions]
  (let [[f & r] remaining-actions
        sp (when f (get-open-subproblem-instance initial-state f))]
    [(SubproblemEntry 
      (unchecked-add (int (if sp (System/identityHashCode sp) 0)) 
                     (unchecked-multiply (int 13) (int (hash r))))
      initial-state reward sp r)
     reward]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Drivers  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahucs-simple [henv]
  (let [e     (hierarchy/env henv)
        init  (env/initial-logging-state e)]
    (binding [*subproblem-cache* (HashMap.)]
      (let [tla (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
            top (make-open-subproblem [:init] init tla)
            result (sub-refine top Double/NEGATIVE_INFINITY)]
        (when (not (number? result))
          (second result))))))

;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 