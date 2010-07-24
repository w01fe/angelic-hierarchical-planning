(ns exp.explicit-angelic-incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy]
            [exp.incremental-search :as is]
            [exp.hierarchical-incremental-search :as his])
  (:import  [java.util HashMap]))


; Hierarchical algorithms that use explicit angelic valuations.
; Note: simple versions that only use optimistic descriptions are still in hierarchical-incremental-search.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; PN-Style simple explicit DASH-A* ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is just like the version in hierarchical-incremental-search, except rather 
; than always choosing the first option at AND-nodes, we choose the one with the 
; minimum number of (tree-counted) leaves with the optimal value. changes marked with
; CHANGED

(defprotocol ConspiracyNumbered
  (conspiracy-number [n]))

(deftype CNSummary [reward cn]
  Comparable         (compareTo  [x] (- (is/max-reward x) reward))
  is/Summary         (max-reward       [] reward)
  ConspiracyNumbered (conspiracy-number [] cn))

(def worst-cn-summary (CNSummary is/neg-inf 1))
(def failed-cn-search (is/make-failed-search worst-cn-summary))

(extend exp.incremental_search.Node
  ConspiracyNumbered {:conspiracy-number (constantly 1)})

(defn min-cn-summaries
  ([] worst-cn-summary)
  ([s] s)
  ([s1 s2]
    (cond (> (is/max-reward s1) (is/max-reward s2)) s1
          (> (is/max-reward s2) (is/max-reward s1)) s2
          (= (is/max-reward s1) is/neg-inf)         s1
          :else (CNSummary (is/max-reward s1) (+ (conspiracy-number s1) (conspiracy-number s2)))))
  ([s1 s2 & more] (reduce min-cn-summaries s1 (cons s2 more))))

(defn add-cn-summaries [s1 s2]
  (let [rew (+ (is/max-reward s1) (is/max-reward s2))]
    (if (= rew is/neg-inf) worst-cn-summary   
        (CNSummary rew (min (conspiracy-number s1) (conspiracy-number s2))))))

(declare get-explicit-cn-dash-sps-search)

(defn get-explicit-cn-dash-sas-map "Get a map from outer final states to SAS nodes/" [hfs]
  (util/cache-with his/*problem-cache* (his/hfs-name hfs) ; unabstracted state SA cache
    (util/map-keys #(env/transfer-effects (:state hfs) %)
      (util/cache-with his/*problem-cache* (his/hfs-first-sub-name hfs) ; abstracted state SA cache
        (let [inner-hfs (his/hfs-first-sub hfs)
              next-hfs (lazy-seq (his/hfs-children inner-hfs))]
          (into {}
                (for [[ss sr] (his/hfs-optimistic-map inner-hfs)]
                  [ss  (is/cache-incremental-search
                        (is/make-custom-recursive-sr-search ; CHANGED 
                         (his/hfs->simple-node inner-hfs ss false sr)
                         (fn [_] (for [n next-hfs :when (his/hfs-can-reach? n ss)] 
                                   (his/hfs->simple-node n ss)))
                         #(apply get-explicit-cn-dash-sps-search (:data %))
                         min-cn-summaries))])))))))

;; Note: may legitimately get to wrong final-state, if some refs reach some states.
;(def *bad-args* nil)
(defn get-explicit-cn-dash-sas-search [hfs final-state] 
  (if-let [f ((get-explicit-cn-dash-sas-map hfs) final-state)]
    (f)
    failed-cn-search))


;; TODO: remove expensive names.
(defn get-explicit-cn-dash-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions hfs)))]
    (if (util/singleton? r-a)
      (get-explicit-cn-dash-sas-search hfs final-state)
      (is/get-cached-search his/*problem-cache* (his/hfs-name hfs final-state)
        (let [outer-cache (get-explicit-cn-dash-sas-map (his/first-action-hfs hfs))]
          (is/make-custom-recursive-sr-search (his/hfs->simple-node hfs [::F final-state]) ;CHANGED
           (fn [_] (map #(his/hfs->simple-node hfs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-explicit-cn-dash-sps-search (his/rest-actions-hfs hfs ss) final-state)                
                 (fn [x y] (min-key (comp conspiracy-number is/current-summary) x y)) ; CHANGED
                 add-cn-summaries ; CHANGED
                 (fn [g1 g2] 
                   (his/hfs->simple-node (his/join-hfs hfs (first (:data g1)) (first (:data g2)) final-state) 
                                         :goal)))))
           min-cn-summaries))))))


(defn make-explicit-cn-dash-a*-search [root-hfs]
  (get-explicit-cn-dash-sas-search root-hfs (util/safe-singleton (keys (his/hfs-optimistic-map root-hfs)))))

(defn explicit-cn-dash-a* [henv] (his/hierarchical-search henv make-explicit-cn-dash-a*-search true first))

(comment
  (use '[exp env hierarchy hierarchical-incremental-search explicit-angelic-incremental-search] 'exp.2d-manipulation 'edu.berkeley.ai.util)
  
  (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
    (doseq [alg `[explicit-simple-dash-a* explicit-cn-dash-a* ]]
      (time (println alg (run-counted #(debug 0 (second ((resolve alg) h))))))))
  
  (let [e (make-random-2d-manipulation-env 3 2) _ (print-state (initial-state e)) h (make-2d-manipulation-hierarchy e)]  
;    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
    (doseq [alg `[explicit-simple-dash-a* explicit-cn-dash-a* ]]
      (time (println alg (run-counted #(debug 0 (second ((resolve alg) h))))))))
  )

; TODO: why exactly is this different from GA* ?? ?
; DASH-A* is a specific application (i.e., set of rules)
; to a strictly improved version of A*LD?
; (in which increases in context bounds are taken into account).
; (sort of)??
; What happens if we try to apply HA*LD with the right hierarchy ? 
; inverted is an instance; others are not ?




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; explicit simple weighted DASH-A* ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the most straightforward application of wA* to the version of dash-A* in
; hierarchical-incremental-search.  We replace max-reward with max(opt * (1 + alpha * a_w), pess),
; where a_w is an optional action weight between 0 and 1.  We do not attempt to compute
; the true f-values.  This means no hard commitments, no adaptive weights. 

; Function from action to weight (> 1).
(def *weight-fn* nil)

(defprotocol SimpleWeighted
  (pess-reward [n])
  (max-gap [n]))

(deftype SWSummary [wtd-reward pes-reward mx-gap]
  Comparable      (compareTo [x] 
                    (let [d (- (is/max-reward x) wtd-reward)]
                      (if (zero? d) (- (pess-reward x) pes-reward) d)))
  is/Summary      (max-reward       [] wtd-reward)
  SimpleWeighted  (pess-reward [] pes-reward)
                  (max-gap [] mx-gap))

(def worst-sw-summary (SWSummary is/neg-inf is/neg-inf 0))
(def failed-sw-search (is/make-failed-search worst-sw-summary))

(deftype SWNode [name wtd-reward pes-reward gap goal? data]
  Comparable (compareTo  [x] 
               (let [c  (- (is/max-reward x) wtd-reward)]
                 (if (not (zero? c)) c
                   (cond goal? -1 
                         (and (instance? exp.incremental_search.Node x) (is/node-goal? x)) 1
                         :else (- (pess-reward x) pes-reward)))))
  is/Summary (max-reward [] wtd-reward)   
  is/Node    (node-name  [] name)
          (node-goal? [] goal?)
  SimpleWeighted (pess-reward [] pes-reward)
                 (max-gap     [] gap))

(defn hfs->leaf-sw-node [hfs ss pes-reward opt-reward]
;  (println pes-reward (max pes-reward (* opt-reward (*weight-fn* (util/safe-singleton (:remaining-actions hfs))))) opt-reward)
  (SWNode (conj (his/hfs-name hfs) ss)
          (max pes-reward (* opt-reward (*weight-fn* (util/safe-singleton (:remaining-actions hfs)))))
          pes-reward (- opt-reward pes-reward) false [hfs ss]))

(defn hfs->goal-sw-node [hfs ss]
  (SWNode (conj (his/hfs-name hfs) ss) (:reward hfs) (:reward hfs) 0 true [hfs ss]))

(defn hfs->temp-sw-node [hfs ss]
  (if (empty? (:remaining-actions hfs))
      (hfs->goal-sw-node hfs ss)
      (SWNode (conj (his/hfs-name hfs) ss) is/pos-inf is/pos-inf 0 false [hfs ss])))

(defn add-sw-summaries [s1 s2]
  (let [rew (+ (is/max-reward s1) (is/max-reward s2))]
    (if (= rew is/neg-inf) worst-sw-summary   
        (SWSummary rew (+ (pess-reward s1) (pess-reward s2)) (max (max-gap s1) (max-gap s2))))))


(defn hfs-angelic-map [hfs]
  (let [{:keys [state remaining-actions]} hfs
        opt  (env/optimistic-map (util/safe-singleton remaining-actions) state)
        pess (env/pessimistic-map (util/safe-singleton remaining-actions) state)]
    (into {} (for [[s r] opt] [s [(get pess s is/neg-inf) r]]))))

(declare get-explicit-sw-dash-sps-search)

(defn get-explicit-sw-dash-sas-map "Get a map from outer final states to SAS nodes" [hfs]
  (util/cache-with his/*problem-cache* (his/hfs-name hfs) ; unabstracted state SA cache
    (util/map-keys #(env/transfer-effects (:state hfs) %)
      (util/cache-with his/*problem-cache* (his/hfs-first-sub-name hfs) ; abstracted state SA cache
        (let [inner-hfs (his/hfs-first-sub hfs)
              next-hfs (lazy-seq (his/hfs-children inner-hfs))]
          (into {}
                (for [[ss [pr or]] (hfs-angelic-map inner-hfs)]
                  [ss  (is/cache-incremental-search
                        (is/make-recursive-sr-search
                         (hfs->leaf-sw-node inner-hfs ss pr or)
                         (fn [_] (for [n next-hfs :when (his/hfs-can-reach? n ss)] 
                                   (hfs->temp-sw-node n ss)))
                         #(apply get-explicit-sw-dash-sps-search (:data %))))])))))))

;; Note: may legitimately get to wrong final-state, if some refs reach some states.
;(def *bad-args* nil)
(defn get-explicit-sw-dash-sas-search [hfs final-state] 
  (if-let [f ((get-explicit-sw-dash-sas-map hfs) final-state)]
    (f)
    failed-sw-search))


;; TODO: remove expensive names.
(defn get-explicit-sw-dash-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions hfs)))]
    (if (util/singleton? r-a)
      (get-explicit-sw-dash-sas-search hfs final-state)
      (is/get-cached-search his/*problem-cache* (his/hfs-name hfs final-state)
        (let [outer-cache (get-explicit-sw-dash-sas-map (his/first-action-hfs hfs))]
          (is/make-recursive-sr-search (hfs->temp-sw-node hfs [::F final-state])
           (fn [_] (map #(hfs->temp-sw-node hfs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-explicit-sw-dash-sps-search (his/rest-actions-hfs hfs ss) final-state)                
                 (fn [x y] (max-key (comp max-gap is/current-summary) x y)) ; CHANGED
                 add-sw-summaries ; CHANGED
                 (fn [g1 g2] 
                   (hfs->goal-sw-node (his/join-hfs hfs (first (:data g1)) (first (:data g2)) final-state) :goal)))))))))))


(defn make-explicit-sw-dash-a*-search [root-hfs]
  (get-explicit-sw-dash-sas-search root-hfs (util/safe-singleton (keys (his/hfs-optimistic-map root-hfs)))))

(defn explicit-sw-dash-a* 
  ([henv weight] (explicit-sw-dash-a* henv weight (constantly 1)))
  ([henv weight action-wt-fn]
     (assert (>= weight 1))
     (binding [*weight-fn* #(inc (* (dec weight) (action-wt-fn %)))]
      (his/hierarchical-search henv make-explicit-sw-dash-a*-search true first))))


(comment
  (use '[exp env hierarchy hierarchical-incremental-search explicit-angelic-incremental-search] 'exp.2d-manipulation 'edu.berkeley.ai.util)
  


  (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
       (doseq [f  [explicit-simple-dash-a* explicit-cn-dash-a* #(explicit-sw-dash-a* % 2) ]]
        (time (println f (run-counted #(debug 0 (second (f h))))))))
  
  (let [e (make-random-2d-manipulation-env 3 5) _ (print-state (initial-state e)) h (make-2d-manipulation-hierarchy e)]  
;    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
       (doseq [f  [explicit-simple-dash-a* explicit-cn-dash-a* #(explicit-sw-dash-a* % 2) ]]
        (time (println f (run-counted #(debug 0 (second (f h))))))))
  )





; Ideally, each node would keep: 
;  - max opt reward
;  - max pess reward
;  - max f' reward
;   - max opt-pess gap of any leaf in tie-broken plan (with max pess).
; (Note: all three can be from different plans.)
; If we always expand in terms of f', we are guaranteed to get alpha-suboptimal solution.
; but: no commitment, rebalancing, etc.  
; Commitment still important since f' values are inconsistent, etc. 


;; TODO: right now we eval every primitive twicE?  