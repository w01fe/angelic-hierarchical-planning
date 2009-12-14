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

;; TODO: logging on state should still support correct equality (i.e., on merged state). 
 ;; Should do effects on state, plus keep separate map.
;; TOOD: look if unwrapping & rewrapping is right.


(defn- sahtn-do-action [cache s a]
  "Return a map from (possibly abstracted) outcome states 
   (with local solutions as metadata) to rewards.
   Takes (possibly abstracted) states as input."
;  (println "DA" (env/action-name a))
  (cond (env/primitive? a)
          (if-let [[ss r]  (and (env/applicable? a s) (env/successor a s))] {(vary-meta ss assoc :opt [a]) r} {})
        (hierarchy/cycle-level a s)                       ; loopy!
          (let [level  (hierarchy/cycle-level a s)
                q      (queues/make-graph-search-pq)
                result (HashMap.)]
;            (println "\n\nstarting!")
            (queues/pq-add! q [s [a]] 0)
            (while (not (queues/pq-empty? q))
;               (println "\n"(queues/pq-size q))
              (let [[[s a] c] (queues/pq-remove-min-with-cost! q)]
;                (println (env/as-map s) (map env/action-name a) c)
                (if (empty? a) 
                    (.put result s (- c))
                  (let [[f & r] a
                        f-level (hierarchy/cycle-level f s)]
;                    (println level f-level (env/action-name f))
                    (assert (or (not f-level) (<= f-level level)))
                    (if (or (not f-level) (< f-level level))
                        (doseq [[ss sr] (sahtn-action cache s f (- c))]
;                          (println "adding" (env/as-map ss) (map env/action-name r))
                           (queues/pq-add! q [ss r] (- sr)))
                      (doseq [ref (hierarchy/immediate-refinements f s)]
;                        (println "adding2" (map env/action-name (concat ref r)))
                         (queues/pq-add! q [s (concat ref r)] c)))))))
            (into {} result))
        :else
           (apply util/merge-with-pred > 
                (for [ref (hierarchy/immediate-refinements a s)]
                  (reduce (fn [cv a] 
                            (apply util/merge-with-pred >  
                                   (for [[s r] cv] (sahtn-action cache s a r))))
                          {s 0} ref)))))


(defn- sahtn-action [#^HashMap cache s a r]
  "Handling boring things - caching and stitching states, etc."
  (let [context-schema  (env/precondition-context a s)
        context         (env/extract-context s context-schema)
	cache-key       [(env/action-name a) context]
	cache-val       (.get cache cache-key)]
;    (println (env/action-name a) "\n" context-schema "\n" context "\n\n" cache-val)
  ;  (println "\nresult for" (env/action-name a))
    (util/map-map 
        (fn [[effect-map local-reward]]
          [(vary-meta (env/apply-effects s effect-map)
                      assoc :opt (concat (:opt (meta s)) (:opt (meta effect-map))))
           (+ r local-reward)])
        (or cache-val
            (let [result
                  (util/map-keys
                   (fn [outcome-state]
                     (with-meta (env/extract-effects outcome-state context-schema) 
                       (select-keys (meta outcome-state) [:opt]))) 
                   (sahtn-do-action cache (env/get-logger s) a))]
              (.put cache cache-key result)
              result)))))




(defn sahtn-dijkstra [henv]
  (let [e       (hierarchy/env henv)
        cache   (HashMap.)
        _       (def *cache* cache)
        results (sahtn-action cache (env/initial-state e) (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]) 0)]
    (when-not (empty? results)
;      (assert (= (count results) 1))
      (let [[k v] (util/first-maximal-element val results)]
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
