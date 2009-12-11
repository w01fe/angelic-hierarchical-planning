(ns exp.sahtn-simple
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [hierarchy :as hierarchy]])
  (:import [java.util HashMap])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    SAHTN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version implementes the usual solution to GHI - only cache when 
;; no loops were involved in the calculation of the result.
; Will be exponentially slow in some recursive heirarcies.

;; All functions are same as sahtn-nr.clj, except merge-valuations has meta
;; added (instead of merge-with-pred >, and sahtn-action does loop-checking stuff.

(defn- merge-valuations [& vs]
  "Like merge-with max, but preserves metadata of the best key."
  (with-meta (apply util/merge-with-pred > vs)
    {:dirty-set (set (apply concat (map #(:dirty-set (meta %)) vs)))}))




(declare sahtn-action)


(defn- sahtn-do-action [cache s a]
  "Return a map from (possibly abstracted) outcome states 
   (with local solutions as metadata) to rewards.
   Takes (possibly abstracted) states as input."
  (if (env/primitive? a)
    (if-let [[ss r] (and (env/applicable? a s) (env/successor a s))] 
        {(vary-meta ss assoc :opt [a]) r} {})
      (apply merge-valuations
        (for [ref (hierarchy/immediate-refinements a s)]
          (reduce (fn [cv a] 
                    (apply merge-valuations
                           (for [[s r] cv] (sahtn-action cache s a r))))
                  {s 0} ref)))))



(defn- sahtn-action [#^HashMap cache s a r]
  "Handling boring things - caching and stitching states, etc."
;  (println s)
  (let [context-schema  (env/precondition-context a)
        context         (env/extract-context s context-schema)
	cache-key       [(env/action-name a) context]
	cache-val       (.get cache cache-key)
        result          
        (or cache-val
         (do (.put cache cache-key (with-meta {} {:dirty-set [cache-key]}))           
             (let [direct-result  (sahtn-do-action cache (env/get-logger s) a)
                   result
                   (util/map-keys
                    (fn [outcome-state]
                      (with-meta (env/extract-effects outcome-state context-schema) (meta outcome-state))) 
                    direct-result)
                   dirty-set (disj (or (:dirty-set (meta direct-result)) #{}) cache-key)]
;               (when (empty? dirty-set) (println cache-key (count dirty-set) result (map meta (keys result))))
               (if (empty? dirty-set) 
                   (.put cache cache-key result)
                 (.remove cache cache-key))
               (with-meta result {:dirty-set dirty-set}))))]
    (with-meta 
      (util/map-map 
       (fn [[effect-map local-reward]]
         [(vary-meta (env/apply-effects s effect-map)
                     assoc :opt (into (or (:opt (meta s)) []) (:opt (meta effect-map))))
          (+ r local-reward)])
       result)
      (meta result))))




(defn sahtn-simple [henv]
  (let [e       (hierarchy/env henv)
        cache   (HashMap.)
        results (sahtn-action cache (env/initial-state e) 
                              (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)]) 0)]
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
