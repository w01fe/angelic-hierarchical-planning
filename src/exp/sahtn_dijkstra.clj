(ns exp.sahtn-dijkstra
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.queues :as queues]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHTN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This  version switches to dijkstra mode when it hits a recursive HLA
; (not yet implemented)

;; TODO: can actually use a consistent heuristic to prune (?) seems not. 

;; In fact, we care about "cycles" in (context, HLA) pairs, not just recursive HLAs.
;; Recursive hierarchies don't cause problems as long as we're guaranteed to make progress. 

;; We need to know two things: 
;;  - When a (context, HLA) pair potentially leads to a cycle 
  ;; (e.g., we'd get a repeat of sahtn-action on the call stack.)
;; - When we get to exit this cycle 
;;   (obvious for acyclic actions, but ideally we can exit this cycle into another cycle.)
;; For now, could assume: (partial order on HLAs + cyclic markings).  
;; For simplicity, assume we assign each HLA a "level" and a "cycle" tag.  

;; TODO: if we know an HLA has a single output state, we can stop sooner in Dijstras. 

(declare sahtn-action)


(defn- sahtn-do-action [cache s a]
  "Return a map from (possibly abstracted) outcome states 
   (with local solutions as metadata) to rewards.
   Takes (possibly abstracted) states as input."
  (cond (satisfies? env/PrimitiveAction a)
          (if-let [[ss r] (env/successor a s)] {(vary-meta ss assoc :opt [a]) r} {})
        (hierarchy/cycle-level a s)                       ; loopy!
          (let [level  (hierarchy/cycle-level a s)
                q      (queues/make-graph-search-pq)
                result (HashMap.)]
            (queues/pq-add! q [s [a]] 0)
            (while (not (queues/pq-empty? q))
              (let [[[s a] c] (queues/pq-remove-min-with-cost! q)]
                (if (empty? a) 
                    (.put result s (- c))
                  (let [[f & r] a
                        f-level (hierarchy/cycle-level f s)]
                    (assert (or (not f-level) (<= f-level level)))
                    (if (or (nil? f-level) (< f-level level))
                        (doseq [[ss sr] (sahtn-action cache s f (- c))]
                          (queues/pq-add! q [ss r] (- sr)))
                      (doseq [ref (hierarchy/immediate-refinements f s)]
                        (queues/pq-add! q [s (concat ref r)] c)))))))
            (into {} result))
        :else          
          (do (util/sref-set! hierarchy/*ref-counter* (inc (util/sref-get hierarchy/*ref-counter*)))
              (apply util/merge-with-pred > 
                (for [ref (hierarchy/immediate-refinements a s)]
                  (do (util/sref-set! hierarchy/*plan-counter* 
                                      (inc (util/sref-get hierarchy/*plan-counter*)))
                      (reduce (fn [cv a] 
                                (apply util/merge-with-pred >  
                                       (for [[s r] cv] (sahtn-action cache s a r))))
                              {s 0} ref)))))))


(defn- sahtn-action [cache s a r]
  "Handling boring things - caching and stitching states, etc."
  (let [context-vars    (set (env/precondition-context a))
        s-map           (env/as-map s)       
        context         (select-keys s-map context-vars)
	cache-key       [(env/action-name a) context]
	cache-val       (.get cache cache-key)]
    (util/map-map 
     (fn [[effect-map local-reward]]
       [(vary-meta (env/apply-effects s effect-map)
                   assoc :opt (into (or (:opt (meta s)) []) (:opt (meta effect-map))))
        (+ r local-reward)])
     (or cache-val
         (let [result
               (util/map-keys
                (fn [outcome-state]
                  (with-meta (env/get-logging-state-puts outcome-state) (meta outcome-state))) 
                (sahtn-do-action cache (env/wrap-logging-state s-map) a))]
             (.put cache cache-key result)
             result)))))




(defn sahtn-dijkstra [henv]
  (let [e       (hierarchy/env henv)
        cache   (HashMap.)
        results (sahtn-action cache (env/initial-state e) (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]) 0)]
    (when-not (empty? results)
      (assert (= (count results) 1))
      (let [[k v] (first results)]
        [(:opt (meta k)) v]))))



; Issue: may be more than one effect map that solves each HLA - and bigger ones will typically be more expensive.  This causes a collision, which could be fixed by using merge-valuations rather than map-keys.  
; But, seems like this should be unnecessary. 

; Things are simpler when we always set all variables.  When not, we have two options:
 ; A variable can be part of a context even when it's never tested in any precondition.  
   ; Suppose we have action "set x to 5", can take it or not.  
   ; Cost to reach "x = 5" depends on value of x in initial state.
 ; OR, we keep track of sets as bona fide part of state.  
; Choose former for now..

; IMPORTANT: as-is, subject to GHI problem ?
; How can we fix this ???

; Can do old fix to GHI but this will mean inefficiency (exponentially?)
; More or less ahve to run Disjkstra
;  Can't really generalize to other states, exxcept those on an optimal path
;  to all goal states at current level. 

; In sparse graphs, note n*Dijkstra is best alg. for APSP. 
