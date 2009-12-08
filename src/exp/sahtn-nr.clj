(ns exp.sahtn-nr
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHTN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version will loop forever on recursive hierarchies


(defn- merge-valuations [& vs]
  "Like merge-with max, but preserves metadata of the best key."
  (reduce 
     (fn [v1 v2] 
       (reduce 
        (fn [v1 [k v]]
          (if (<= v (get v1 k Double/NEGATIVE_INFINITY))
	    v1
            (assoc (dissoc v1 k) k v)))
        v1 v2))
     (or (first vs) {}) (rest vs)))



(declare sahtn-plan)

(defn- sahtn-do-action [cache s a]
  "Return a map from (possibly abstracted) outcome states 
   (with local solutions as metadata) to rewards.
   Takes (possibly abstracted) states as input."
  (if (satisfies? env/PrimitiveAction a)
    (if-let [[ss r] (env/successor a s)] {(vary-meta ss assoc :opt [a]) r} {})
    (do (util/sref-set! hierarchy/*ref-counter* (inc (util/sref-get hierarchy/*ref-counter*)))
        (apply merge-valuations
               (for [ref (hierarchy/immediate-refinements a s)]
                 (do (util/sref-set! hierarchy/*plan-counter* (inc (util/sref-get hierarchy/*plan-counter*)))
                     (sahtn-plan cache {s 0} ref)))))))

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

(defn- sahtn-plan [cache v as]
  "Return a map from (possibly abstracted) output states 
   (with opt. sols. as metadata) to rewards."
  (reduce (fn [cv a] 
            (apply merge-valuations 
                   (for [[s r] cv] (sahtn-action cache s a r))))
          v as))


(defn sahtn-nr [henv]
  (let [e       (hierarchy/env henv)
        cache   (HashMap.)
        results (sahtn-plan cache {(env/initial-state e) 0} (hierarchy/initial-plan henv))]
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
