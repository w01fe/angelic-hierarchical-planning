(ns exp.sahdd
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy])
  (:import  [java.util HashMap]))

; Here, there is no real Seq character.  No real choices.  
; Note: hard (impossible?) to unify down and up.
; Best: at least have common interface, shared parts, to simplify.

;; Also pass in antagonistic measure ? 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queues ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-queue [initial-elements]
  (let [q (queues/make-graph-search-pq)]
    (queues/g-pq-add! q :dummy Double/POSITIVE_INFINITY)
    (queues/pq-add-all! q initial-elements)
    q))

(defn empty-queue [queue]
  (queues/pq-remove-all! queue)
  (queues/g-pq-replace! queue :dummy Double/POSITIVE_INFINITY))

(defn queue-best-reward [queue]
  (- (nth (queues/g-pq-peek-min queue) 1)))

(defn queue-best-and-next-reward [queue]
  (let [[best bc] (queues/pq-remove-min-with-cost! queue)
        next-reward (queue-best-reward queue)]
    (queues/pq-replace! queue best bc)
    [best next-reward]))

(defn queue-cutoff? [queue reward-threshold]
  (let [cutoff (double (queue-best-reward queue))]
    (or (= cutoff Double/NEGATIVE_INFINITY) (< cutoff reward-threshold))))

(defn refine-open [child-queue goal-atom goal-fn expand-fn reward-fn single-goal? reward-threshold]
  (when-not (queue-cutoff? child-queue reward-threshold)
    (let [[best next-best-reward] (queue-best-and-next-reward child-queue)]
      (if-let [g (goal-fn best)]
            (do (when single-goal? (empty-queue child-queue))
                (queues/pq-remove! child-queue best) ;; TODO: Is this always right? 
                (assert (not (contains? @goal-atom g)))
                (swap! goal-atom assoc g (reward-fn best)))
          (do (queues/pq-add-all! child-queue 
                                  (for [x (expand-fn best (max next-best-reward reward-threshold))]
                                    [x (- (reward-fn x))]))
              (let [r (reward-fn best)] 
                (if (= r Double/NEGATIVE_INFINITY) 
                    (queues/pq-remove! child-queue best)
                  (queues/pq-replace! child-queue best (- r))))))
      (recur child-queue goal-atom goal-fn expand-fn reward-fn single-goal? reward-threshold))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Outcome maps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn stitch-outcome-map [outcome-map state reward-to-state]
  (util/map-map1 
   (fn [[outcome-state local-reward]]
     [(vary-meta (env/apply-effects state (env/extract-effects outcome-state)) assoc 
                 :opt (concat (:opt (meta state)) (:opt (meta outcome-state))))
      (+ reward-to-state local-reward)]) 
   outcome-map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblems ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defprotocol Subproblem 
  (sub-reward-threshold [sp last-threshold])
  (sub-refine           [sp last-threshold new-threshold]))

(declare se-goal se-reward-threshold se-refine)

(defn pretty-state [s]
  (dissoc (env/as-map (or s {})) :const))

(deftype OpenSubproblem [name child-queue result-atom single-goal?] :as this
  Subproblem
  (sub-reward-threshold [last-threshold]
    (let [queue-reward (queue-best-reward child-queue)]
      (if (>= last-threshold queue-reward) queue-reward
          (apply max queue-reward (filter #(< % last-threshold) (vals @result-atom))))))
  (sub-refine           [last-threshold new-threshold]
    (println "\nRefining " (second  name) (first name) "\n" (util/map-keys pretty-state @result-atom)  "\n"(map #(cons (pretty-state (:initial-state (first %))) (next %)) (queues/pq-peek-pairs child-queue)))
;    (println "\nRefining " (second  name) (first name) "\n" (util/map-keys identity @result-atom)  "\n"(map #(cons (identity (first %)) (next %)) (queues/pq-peek-pairs child-queue)))    
    (refine-open child-queue result-atom se-goal se-refine se-reward-threshold single-goal? new-threshold)
    (println "\nDONE Refining " (second  name) (first name) "\n" (util/map-keys pretty-state @result-atom)  "\n" (map #(cons (pretty-state (:initial-state (first %))) (next %)) (queues/pq-peek-pairs child-queue)))
    (util/filter-map #(and (<= new-threshold (val %)) (< (val %) last-threshold)) @result-atom)))

(declare make-subproblem-entry)

(defn make-open-subproblem [name state action single-goal?]
  (if (env/primitive? action)
    (OpenSubproblem name
     (make-queue nil)
     (atom (if-let [[ss r] (and (env/applicable? action state) (env/successor action state))] {ss r} {}))
     single-goal?)
    (OpenSubproblem name
     (make-queue (for [ref (hierarchy/immediate-refinements action state)]
                   [(make-subproblem-entry state 0.0 ref) 0.0]))
     (atom {})
     single-goal?)))


(def #^HashMap *subproblem-cache*)

(defmacro get-subproblem-instance [name & body]
  `(let [name# ~name
         inst# (find *subproblem-cache* name#)]
     (if inst# (nth inst# 1)
       (let [x# (do ~@body)]
         (.put *subproblem-cache* name# x#)
         x#))))

(defn create-open-subproblem [state action]
  (let [context   (env/precondition-context action state)
        name     [(env/extract-context state context) (env/action-name action)]]
    (get-subproblem-instance name (make-open-subproblem name (env/get-logger state context) action false))))

; SAS, SAAS, SASAS
;(defmulti create-subproblem (fn [state action ...])) ?



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Subproblem Entries ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol SubproblemEntry
  (se-goal             [se])
  (se-reward-threshold [se])
  (se-refine           [se new-threshold]))

(deftype SubproblemSolutionEntry [initial-state reward]
  Object
  (equals [y] (= initial-state (:initial-state y)))
  (hashCode [] (hash initial-state))
  SubproblemEntry
  (se-goal             [] initial-state)
  (se-reward-threshold [] reward)
  (se-refine           [new-threshold] (throw (RuntimeException. "Not refinable"))))



(deftype SubproblemPartialEntry [hash-code last-cutoff-atom initial-state reward child-subproblem remaining-actions] :as this
  Object
  (equals [y] (or (identical? this y) 
                  (and (identical? child-subproblem (:child-subproblem y)) 
                       (= remaining-actions (:remaining-actions y)))))
  (hashCode [] hash-code)
  SubproblemEntry
  (se-goal     [] nil)
  (se-reward-threshold [] @last-cutoff-atom #_(+ reward (sub-reward-threshold child-subproblem @last-cutoff-atom)))
  (se-refine           [reward-cutoff]
    (let [results     (sub-refine child-subproblem @last-cutoff-atom (- reward-cutoff reward))]
      (reset! last-cutoff-atom (- reward-cutoff reward))
      (println "got " results " new cutoff " (se-reward-threshold this))
      (for [[s r] (stitch-outcome-map results initial-state reward)]
        (make-subproblem-entry s r remaining-actions)))))

(defn make-subproblem-entry [initial-state reward remaining-actions]
  (if (empty? remaining-actions) 
      (println "DONE"  initial-state reward)
    (println "PARTIAL" initial-state reward (map env/action-name remaining-actions))
      )
  (if-let [[f & r] (seq remaining-actions)]
    (let [sp (create-open-subproblem initial-state f)]
      (SubproblemPartialEntry 
       (unchecked-add (int (System/identityHashCode sp)) 
                      (unchecked-multiply (int 13) (int (hash r))))
       (atom Double/POSITIVE_INFINITY) initial-state reward sp r))
    (SubproblemSolutionEntry initial-state reward)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Drivers  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sahucs-simple [henv]
  (let [e     (hierarchy/env henv)
        init  (env/initial-logging-state e)]
    (binding [*subproblem-cache* (HashMap.)]
      (when-first [p (sub-refine (make-open-subproblem [:init] init  
                                   (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]) true)
                                 Double/POSITIVE_INFINITY Double/NEGATIVE_INFINITY)]
        (second p)))))

;; For SAHA, nothing is open.
;  Or strcture is same.
 ; Goal is: ?
 ; Can we look at clause-based algs as in-between SAHA and SAHUCS ? 