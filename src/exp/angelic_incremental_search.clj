(ns exp.angelic-incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy]
            [exp.incremental-search :as is]
            [exp.hierarchical-incremental-search :as his])
  (:import  [java.util HashMap]))


; Hierarchical algorithms that can use non-concrete angelic valuations.

; (require optimistic & pessimistic in line, by single map from clauses to [p o] pairs) ?
; Still have correspondence problem.
; unless: require single "region"/clause.  All existing hierarchies had this anyway ?  

;; TODO: fix paredit key bindings.
;; TODO: formap 

(declare hierarchy/concrete-clause?) ;; Clause is also a state
(declare hierarchy/can-refine-from?) ; Is clause concrete enough to meaningfully refine this action?
(declare hierarchy/immediate-refinements-clause) ; Returns seq of [constraint ref] pairs from this clause.
(declare hierarchy/next-clause-and-rewards) ; takes action & clause, returns [result-clause [pess-rew opt-rew]]
(declare hierarchy/restrict-clause) ;; Takes clause & constraint; returns nil for invalid.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def #^HashMap *problem-cache* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;; Angelic Hierarchical State ;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype AngelicHierarchicalState [in-clause plan primitive? reward-bounds out-clause])

(defn make-ahs [in-clause plan reward-bounds out-clause]
  (AngelicHierarchicalState in-clause plan (every? env/primitive plan) reward-bounds out-clause))

(defn ahs-name [ahs] [(:in-clause ahs) (map env/action-name (:plan ahs))])

(defn make-root-ahs [in-clause action]
  (let [[out-clause reward-bounds] (hierarchy/next-clause-and-rewards action in-clause)]
    (make-ahs in-clause [action] reward-bounds out-clause)))

(defn ahs-refinements [ahs]
  (let [{:keys [in-clause plan primitive? reward-bounds out-clause]} ahs
        a      (util/safe-singleton plan)]
    (assert (not (env/primitive? a)))
    (for [[constraint ref] (hierarchy/immediate-refinements-clause in-clause a)
          :let             [constrained-clause (hierarchy/restrict-clause in-clause constraint)]
          :when            constrained-clause]
      [constraint (make-ahs constrained-clause ref [is/ninf (second reward-bounds)] out-clause)])))

(defn ahs-goal? [ahs] (empty? (:plan ahs)))

(defn split-ahs [ahs]
  (let [{:keys  [in-clause plan primitive? reward-bounds out-clause]} ahs
        [f & r] (util/make-safe (seq plan))]
    
    (for [[constraint ref] (hierarchy/immediate-refinements-clause in-clause a)
          :let             [constrained-clause (hierarchy/restrict-clause in-clause constraint)]
          :when            constrained-clause]
      [constraint (make-ahs constrained-clause ref [is/ninf (second reward-bounds)] out-clause)]))
  )



(defn combine-ahs [n1 n2 state-combiner action-combiner]
  (AngelicHierarchicalState
   (state-combiner       (:state n1)   (:state n2))
   (+                    (:reward n1)  (:reward n2))
   (into                 (:opt-sol n1) (:opt-sol n2))
   (action-combiner      (:remaining-actions n1) (:remaining-actions n2))))

(defn ahs-first-sub-name "Name for first abstracted subproblem of ahs" [ahs]
  (let [{[f] :remaining-actions state :state} ahs]      
    [(env/extract-context state (env/precondition-context f state)) (env/action-name f)]))

(defn ahs-first-sub "First abstracted subproblem of ahs" [ahs]
  (let [{[f] :remaining-actions state :state} ahs]
    (make-root-ahs (env/get-logger state (env/precondition-context f state)) f)))


; used for saha only
(defn first-action-ahs "Return ahs for just first action." [ahs]
  (let [{:keys [state reward opt-sol remaining-actions]} ahs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (AngelicHierarchicalState state 0 nil (take 1 remaining-actions))))

(defn rest-actions-ahs "Return ahs for just first action." [ahs mid-state]
  (let [{:keys [state reward opt-sol remaining-actions]} ahs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (AngelicHierarchicalState mid-state 0 nil (drop 1 remaining-actions))))

(defn join-ahs [first-result rest-result final-state]
  (combine-ahs first-result rest-result (constantly final-state) (constantly nil)))

(defn ahs-optimistic-map [ahs]
  (let [{:keys [state remaining-actions]} ahs]
    (assert (util/singleton? remaining-actions))
    (env/optimistic-map (first remaining-actions) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Fancier Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol PSAHA-Summary
  (min-reward [s])
  (max-gap    [s]))

(defn compare-saha-summaries [x1 x2]
  (let [s1 (- (max-reward x2) (max-reward x1))]
    (if (zero? s1) (- (min-reward x2) (min-reward x1)) s1)))

(deftype SAHA-Summary [min-reward max-reward max-gap] :as this
  Comparable    (compareTo  [x] (compare-saha-summaries this x))
  Summary       (max-reward []  max-reward)
  PSAHA-Summary (min-reward []  min-reward)
                (max-gap    []  max-gap))

(defn add-saha-summaries [s1 s2]
  (SAHA-Sumary 
   (+ (min-reward s1) (min-reward s2))
   (+ (max-reward s1) (max-reward s2)) 
   (max (max-gap s1) (max-gap s2))))

(deftype SAHA-Node [name goal? ahs] :as this
  Comparable (compareTo  [x] 
               (let [c (compare-saha-summaries this x)]
                 (if (zero? c) (compare (and (instance? exp.incremental_search.Node x) (is/node-goal? x)) goal?) c)))
  is/Summary (max-reward [] (nth (:reward-bounds ahs) 1))   
  is/Node    (node-name  [] name)
             (node-goal? [] goal?)
  PSAHA-Summary (min-reward []  (nth (:reward-bounds ahs) 0))
                (max-gap    []  ????))

(defn name-str [x]
  (let [n (:name x)]
    (if (symbol? n) n
        (vec (map #(if (instance? exp.env.FactoredState %) (dissoc (exp.env/as-map %) :const) %) n)))))

(defmethod print-method ::SimpleNode [x s]
  (print-method (str "Nd<" (name-str x) "," (:reward x) "," (:goal? x) ">") s))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; AHS & Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn ahs->node 
  ([ahs] (is/SimpleNode (ahs-name ahs) (:reward ahs) (empty? (:remaining-actions ahs)) ahs))
  ([ahs extra-data] (ahs->simple-node ahs extra-data (empty? (:remaining-actions ahs))))
  ([ahs extra-data goal?] ; for inverted, needs non-goal goal-looking nodes.
     (is/SimpleNode (conj (ahs-name ahs) extra-data) (:reward ahs) goal? [ahs extra-data]))
  ([ahs extra-data goal? rew] ; for saha, needs estimated reward.
     (is/SimpleNode (conj (ahs-name ahs) extra-data) rew goal? [ahs extra-data])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searches ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Idea is similar to saha-simple.  Two main differences:
; 1.  To support clauses, we have to be able to dynamiaclly split.  Eventually, this 
;    should be done by dynamicsally wrapping old nodes.  For now, wej ust use caching.
; 2.  Wince we're only allowing a single output clause per action, we don't need the weird
;    inner/outer cache deal.  

(declare get-saha-cpc-search)

(defn get-saha-cac-search [cac-ahs]
  (is/get-cached-search *problem-cache* (ahs-name cac-ahs)
    (is/make-recursive-sr-search
     (ahs->simple-node cac-ahs)
     #(map ahs->simple-node (ahs-refinements (:data %)))
     #(get-saha-cpc-search (:data %)))))

(defn get-saha-cpc-search [ahs final-state]
;  (println "\nget-sps" ahs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions ahs)))]
    (if (util/singleton? r-a)
      (get-saha-sas-search ahs final-state)
      (is/get-cached-search *problem-cache* (ahs-name ahs final-state)
        (let [outer-cache (get-sas-map (first-action-ahs ahs))]
          (is/make-recursive-sr-search (ahs->simple-node ahs [::F final-state])
           (fn [_] (map #(ahs->simple-node ahs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-saha-sps-search (rest-actions-ahs ahs ss) final-state)                
                 (fn [x y] x)
                 is/add-simple-summaries 
                 (fn [g1 g2] 
                   (ahs->simple-node (join-ahs (first (:data g1)) (first (:data g2)) final-state) 
                                     :goal)))))))))))


(defn get-sas-map "Get a map from outer final states to SAS nodes/" [ahs]
  (util/cache-with *problem-cache* (ahs-name ahs) ; unabstracted state SA cache
    (util/map-keys #(env/transfer-effects (:state ahs) %)
      (util/cache-with *problem-cache* (ahs-first-sub-name ahs) ; abstracted state SA cache
        (let [inner-ahs (ahs-first-sub ahs)
              next-ahs (lazy-seq (ahs-children inner-ahs))]
          (into {}
                (for [[ss sr] (ahs-optimistic-map inner-ahs)]
                  [ss  (is/cache-incremental-search
                        (is/make-recursive-sr-search 
                         (ahs->simple-node inner-ahs ss false sr)
                         (fn [_] (for [n next-ahs :when (ahs-can-reach? n ss)] 
                                   (ahs->simple-node n ss)))
                         #(apply get-saha-sps-search (:data %))))])))))))

(defn get-saha-sas-search [ahs final-state] 
  (((get-sas-map ahs) final-state)))


;; TODO: remove expensive names.
(defn get-saha-sps-search [ahs final-state]
;  (println "\nget-sps" ahs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions ahs)))]
    (if (util/singleton? r-a)
      (get-saha-sas-search ahs final-state)
      (is/get-cached-search *problem-cache* (ahs-name ahs final-state)
        (let [outer-cache (get-sas-map (first-action-ahs ahs))]
          (is/make-recursive-sr-search (ahs->simple-node ahs [::F final-state])
           (fn [_] (map #(ahs->simple-node ahs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-saha-sps-search (rest-actions-ahs ahs ss) final-state)                
                 (fn [x y] x)
                 is/add-simple-summaries 
                 (fn [g1 g2] 
                   (ahs->simple-node (join-ahs (first (:data g1)) (first (:data g2)) final-state) 
                                     :goal)))))))))))


(defn make-saha-search [root-ahs]
  (get-saha-sas-search root-ahs (util/safe-singleton (keys (ahs-optimistic-map root-ahs)))))

;; TODO: version with better meta-level control, PN-style. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)

(defn hierarchical-search 
  ([henv policy search-maker] (hierarchical-search henv policy search-maker identity))
  ([henv policy search-maker ahs-sol-extractor]
     (binding [*node-type-policy* policy
               *problem-cache*    (HashMap.)]
       (let [e    (hierarchy/env henv)
             init (env/initial-logging-state e)
             tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
             top  (search-maker (make-root-ahs init tla))]
         (when-let [sol (is/first-goal-node top)]
           (let [sol-ahs (ahs-sol-extractor (:data sol))]
             [(:opt-sol sol-ahs) (:reward sol-ahs)]))))))

(defn saha-simple [henv]
  (hierarchical-search henv nil make-saha-search first))



(comment
  (do (use '[exp env hierarchy taxi ucs hierarchical-incremental-search] 'edu.berkeley.ai.util) (require '[exp sahucs-simple sahucs-simple-dijkstra sahucs-inverted saha-simple] '[exp.old ahois]))
   (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
    (doseq [alg `[sahucs-flat sahucs-fast-flat exp.sahucs-simple/sahucs-simple sahucs-simple exp.sahucs-simple-dijkstra/sahucs-simple-dijkstra sahucs-dijkstra exp.sahucs-inverted/sahucs-inverted sahucs-inverted exp.saha-simple/saha-simple saha-simple ]]
      (time (println alg (run-counted #(debug 0 (second ((resolve alg) h)))))))))