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

(defn explicit-cn-dash-a* [henv] (his/simple-hierarchical-search henv make-explicit-cn-dash-a*-search true first))

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
(def *sw-weight-fn* nil)

; Here, we only use pess reward for tiebreaking.
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
;  (println pes-reward (max pes-reward (* opt-reward (*sw-weight-fn* (util/safe-singleton (:remaining-actions hfs))))) opt-reward)
  (SWNode (conj (his/hfs-name hfs) ss)
          (max pes-reward (* opt-reward (*sw-weight-fn* (util/safe-singleton (:remaining-actions hfs)))))
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
     (binding [*sw-weight-fn* #(inc (* (dec weight) (action-wt-fn %)))]
      (his/simple-hierarchical-search henv make-explicit-sw-dash-a*-search true first))))


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





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; explicit greedy weighted DASH-A* ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a fancier application of wA* to the version of dash-A* in
; hierarchical-incremental-search.  

; As above, we replace max-reward with max(opt * (1 + alpha * a_w), pess),
; where a_w is an optional action weight between 0 and 1. (should eventually adapt?)

; In addition to this, we also add commitment.  To do this, we must keep track of the 
; max opt reward of any plan, separately of f' or whatever else.  

; Then, whenever any node's max pess reward comes above w * opt, we can commit to that child.
; Doing this within current search could corrupt caches, so instead we extract pessimistic plan,
; decompose, and start new searches (with same shared caches). 


; Function from action to weight (> 1).
(def *gw-weight-fn* nil)

(defprotocol GreedyWeighted
  (best-pess-reward [n] "Best pessimistic reward of any descendent")
  (best-pess-plan   [n] "Corresponding leaf node sequence")
  (best-opt-reward  [n] "Best optimistic reward."))

(deftype GWSummary [wtd-reward pes-reward mx-gap best-pr best-pp best-or]
  Comparable      (compareTo [x] 
                    (let [d (- (is/max-reward x) wtd-reward)]
                      (if (zero? d) (- (pess-reward x) pes-reward) d)))
  is/Summary      (max-reward       [] wtd-reward)
  SimpleWeighted  (pess-reward [] pes-reward)
                  (max-gap [] mx-gap)
  GreedyWeighted  (best-pess-reward [] best-pr)
                  (best-pess-plan   [] best-pp)
                  (best-opt-reward  [] best-or))

(def worst-gw-summary (GWSummary is/neg-inf is/neg-inf 0 is/neg-inf nil is/neg-inf))
(def failed-gw-search (is/make-failed-search worst-gw-summary))

(deftype GWNode [name wtd-reward pes-reward opt-reward gap goal? data] :as this
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
                 (max-gap     [] gap)
  GreedyWeighted  (best-pess-reward [] pes-reward)
                  (best-pess-plan   [] (when (> pes-reward is/neg-inf) [this]))
                  (best-opt-reward  [] opt-reward))


(defn add-gw-summaries [s1 s2]
  (let [rew (+ (is/max-reward s1) (is/max-reward s2))]
    (if (= rew is/neg-inf) worst-gw-summary   
      (let [prew (+ (best-pess-reward s1) (best-pess-reward s2))]
        (GWSummary rew (+ (pess-reward s1) (pess-reward s2)) (max (max-gap s1) (max-gap s2))
                   prew (when (> prew is/neg-inf) (concat (best-pess-plan s1) (best-pess-plan s2)))
                   (+ (best-opt-reward s1) (best-opt-reward s2)))))))

(defn min-gw-summaries [& summaries]
  (let [summaries (remove #(= (is/max-reward %) is/neg-inf) summaries)]
   (if (empty? summaries) worst-gw-summary
       (let [best-wtd (apply max-key is/max-reward summaries)
             best-pess (apply max-key best-pess-reward summaries)]
         (GWSummary 
          (is/max-reward best-wtd) (pess-reward best-wtd) (max-gap best-wtd)
          (best-pess-reward best-pess) (best-pess-plan best-pess) 
          (apply max (map best-opt-reward summaries)))))))


(defn hfs->leaf-gw-node [hfs ss pes-reward opt-reward]
  (GWNode (conj (his/hfs-name hfs) ss)
          (max pes-reward (* opt-reward (*gw-weight-fn* (util/safe-singleton (:remaining-actions hfs)))))
          pes-reward opt-reward (- opt-reward pes-reward) false [hfs ss]))

(defn hfs->goal-gw-node [hfs ss]
  (GWNode (conj (his/hfs-name hfs) ss) (:reward hfs) (:reward hfs) (:reward hfs) 0 true [hfs ss]))

(defn hfs->temp-gw-node [hfs ss]
  (if (empty? (:remaining-actions hfs))
      (hfs->goal-gw-node hfs ss)
      (GWNode (conj (his/hfs-name hfs) ss) is/pos-inf is/neg-inf is/pos-inf 0 false [hfs ss])))



(declare get-explicit-gw-dash-sps-search)

(defn get-explicit-gw-dash-sas-map "Get a map from outer final states to SAS nodes" [hfs]
  (util/cache-with his/*problem-cache* (his/hfs-name hfs) ; unabstracted state SA cache
    (util/map-keys #(env/transfer-effects (:state hfs) %)
      (util/cache-with his/*problem-cache* (his/hfs-first-sub-name hfs) ; abstracted state SA cache
        (let [inner-hfs (his/hfs-first-sub hfs)
              next-hfs (lazy-seq (his/hfs-children inner-hfs))]
          (into {}
                (for [[ss [pr or]] (hfs-angelic-map inner-hfs)]
                  [ss  (is/cache-incremental-search
                        (is/make-custom-recursive-sr-search
                         (hfs->leaf-gw-node inner-hfs ss pr or)
                         (fn [_] (for [n next-hfs :when (his/hfs-can-reach? n ss)] 
                                   (hfs->temp-gw-node n ss)))
                         #(apply get-explicit-gw-dash-sps-search (:data %))
                         min-gw-summaries))])))))))

;; Note: may legitimately get to wrong final-state, if some refs reach some states.
;(def *bad-args* nil)
(defn get-explicit-gw-dash-sas-search [hfs final-state] 
  (if-let [f ((get-explicit-gw-dash-sas-map hfs) final-state)]
    (f)
    failed-gw-search))


;; TODO: remove expensive names.
(defn get-explicit-gw-dash-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions hfs)))]
    (if (util/singleton? r-a)
      (get-explicit-gw-dash-sas-search hfs final-state)
      (is/get-cached-search his/*problem-cache* (his/hfs-name hfs final-state)
        (let [outer-cache (get-explicit-gw-dash-sas-map (his/first-action-hfs hfs))]
          (is/make-custom-recursive-sr-search (hfs->temp-gw-node hfs [::F final-state])
           (fn [_] (map #(hfs->temp-gw-node hfs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-explicit-gw-dash-sps-search (his/rest-actions-hfs hfs ss) final-state)                
                 (fn [x y] (max-key (comp max-gap is/current-summary) x y)) ; CHANGED
                 add-gw-summaries ; CHANGED
                 (fn [g1 g2] 
                   (hfs->goal-gw-node (his/join-hfs hfs (first (:data g1)) (first (:data g2)) final-state) :goal)))))
           min-gw-summaries))))))


(defn make-explicit-gw-dash-a*-search [root-hfs]
  (get-explicit-gw-dash-sas-search root-hfs (util/safe-singleton (keys (his/hfs-optimistic-map root-hfs)))))

(defn first-solution-or-greedy-summary [search greedy?-fn]
;  (println (is/root-node search))
  (let [s (is/current-summary search), mr (is/max-reward s)]
;    (println mr (best-pess-reward s) (best-opt-reward s))
    (cond (and (greedy?-fn s) (> (count (best-pess-plan s)) 1)#_(not (identical? s (is/root-node search))))
            s
          (= mr is/neg-inf) 
            nil
          :else   
            (or (is/next-goal search mr) (recur search greedy?-fn)))))

(declare extract-simple-greedy-solution-from-summary)

(defn extract-simple-greedy-solution-from-node [greedy-node]
  (if (is/node-goal? greedy-node)
      (his/hfs-solution-pair (first (:data greedy-node)))
    (extract-simple-greedy-solution-from-summary
     (first-solution-or-greedy-summary
      (apply get-explicit-gw-dash-sas-search (:data greedy-node))
      #(>= (best-pess-reward %) (best-pess-reward greedy-node))))))

(defn extract-simple-greedy-solution-from-summary [greedy-summary]
#_  (println "got greedy plan!" 
    (for [node (best-pess-plan greedy-summary)
          :let [hfs (first (:data node))]]
      (if (empty? (:remaining-actions hfs) )
          (vec (map env/action-name (:opt-sol hfs)))
        (env/action-name (first (:remaining-actions hfs))))))
  (->> (best-pess-plan greedy-summary)
       (map extract-simple-greedy-solution-from-node)
       (apply env/concat-solution-pairs)))

(defn explicit-gw-dash-a* 
  ([henv weight] (explicit-gw-dash-a* henv weight (constantly 1)))
  ([henv weight action-wt-fn]
     (assert (>= weight 1))
     (binding [*gw-weight-fn* #(inc (* (dec weight) (action-wt-fn %)))]
      (his/generic-hierarchical-search henv 
       (comp extract-simple-greedy-solution-from-summary
             (fn [s] (first-solution-or-greedy-summary 
                      s #(>= (best-pess-reward %) (* weight (best-opt-reward %)))))
             make-explicit-gw-dash-a*-search)))))

;; TODO: really, we should more tightly couple search with things other than weighted f',
; i.e., return upwards whenever pess bound increases.
 ; and, really, f' is not what we want.
 ; f' could have us working on a plan that is neither the nearly commited one, nor the
 ; one contributing to the global bound.
 ; Possible theorem: always want to refine a best node for *some* weight?
 ;  i.e., nearly committed will be best with (near-)infinite weight.  global bound will be weight=1.
 ;  not right either though, best infinite weight plan might not have enough slack to be possibly-optimal.
; Clearly, want to either 
; - work on (max-gap?) node contributing to global bound, OR
; - work on a (max-gap?) node part of a plan with expected lowest cost-to-refine to prove optimal.
;  - probability depends on portion of spread within bound (tough to define where no pess...)
;  - cost depends on size of spread / height of actions / ...?

; Question: is there room for explicit pruning?  Ideally, no -- our refinement criteria takes care of it.
; Pruning criteria: prune any node/search that cannot contribute to wtd-suboptimal solution.

;; TODO: note that without max-gap in ref criteria, we never back out
; plus, inadmissibility means we often get stuck inside a subproblem ...

;; TODO: do we want to commit at subproblem-level as well? 

;; TODO: remove short-circuit from custom!

;; TODO: more general or/and algorithms that let me choose arbitrary best, stopping criteria, etc.
; TODO: algorithm that just alternates between prove-best and disprove-rest, 
; - perhaps using CN for latter
; - perhaps using some sort of inertia for former.  i.e., depth-first-ish (must do and-switch).

; Look at: Finding Acceptable Solutions Faster Using Inadmissible Information
; "Explicit estimation search"

; Here's a concrete proposal:
;  Each leaf has: pessimistic, optimistic, 
;   mapping from reward to 
;     probability that best child achieves >= this, plus
;     if true: expected # of refinements to raise best child pess bound >= this value
;     if false: expected # of refinements to drop best child opt bound < this value. 

;  For an entire plan, given a threshold, we can compute :
;  expected refinements to success ~= (#prove * p + #disprove * (1-p)) / p
;  If we are to refine a pess plan, we should pick the min such plan.
;  To decide to do this or raise the global bound b, we can consider some epsilon,
;    count the number of plans C on the open list with f < b*(1+epsilon),
;  and compare min expected refinements to success now, with
;  C + min expected refinements if bound became b(1+epsilon).
;  We probably want some stochasticity just in case our #prove and #disprove are horribly uncalibrated.

;  For a given sequence of nodes, we can pretend we will decide on (the best) reward breakdown
;  in advance, and stick to that to the bitter end.  
;  This also means we ignore sharing for now, which may turn out to be very important.  
;  Theoretically, for a given reward, want to choose policy that minimizes expected refinements to success (?)
;  To do that, we just range over all breakdowns, multiplying probabilities and adding refs.
;    -- note that if a single node fails, we fail, so we don't add #disproves ?

; One problem with all of this -- may be too greedy in some cases (only a few refinements to dramatically 
; improve bounds on a plan), or not greedy enough in others (?)

; TODO: another problem with these methods in general (as shown above) is out-of-date-ness. 

; In any case, seems doable; we just need: 
 ; distributions for the above quantities
 ; efficient ways to do the necessary convolutions
;  Suppose we just have median reward -- expected is problematic, for obv. reasons.
;  (assume bipartite uniform distribution -- except if no pess, use geom for that side? )
; Now, how do we estimate amount of work we need to do?
 ; Using median reward, (assuming const. action reward), can estimate # of actions in refinement
 ; Plus avg. branching factor, can estimate total refinements, etc.
 ; Also know # of levels (ignoring recursion?)
 ; - assume const. amount of uncertainty goes away at eacy level
 ; - Assume true value is median of remaining distribution, we shrink towards it.
 ; - exponential of # of levels until shrink excludes threshold = value ? 
; Seems like a pretty good idea; in any case, leave it for later. 




(comment
  (use '[exp env hierarchy hierarchical-incremental-search explicit-angelic-incremental-search] 'exp.2d-manipulation 'edu.berkeley.ai.util)
  


  (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
       (doseq [f  [explicit-simple-dash-a* explicit-cn-dash-a* #(explicit-sw-dash-a* % 2) #(explicit-gw-dash-a* % 2) ]]
        (time (println f (run-counted #(debug 0 (second (f h))))))))
  
  (let [e (make-random-2d-manipulation-env 3 5) _ (print-state (initial-state e)) h (make-2d-manipulation-hierarchy e)]  
;    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
       (doseq [f  [explicit-simple-dash-a* explicit-cn-dash-a* #(explicit-sw-dash-a* % 2) #(explicit-gw-dash-a* % 2) ]]
        (time (println f (run-counted #(debug 0 (second (f h))))))))
  )



;; TODO: right now we eval every primitive twicE?  not counted, but perhaps a problem for robotics ...