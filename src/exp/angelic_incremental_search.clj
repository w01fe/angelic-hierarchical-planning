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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Angelic Summary ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


(defn compare-saha-nodes [x1 x2]
  (let [c (compare-saha-summaries x1 x2)]
    (if (zero? c)  
        (compare (and (instance? exp.incremental_search.Node x2) (is/node-goal? x2))
                 (and (instance? exp.incremental_search.Node x1) (is/node-goal? x1)))
        c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CAC Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment 
  (defn name-str [x]
    (let [n (:name x)]
      (if (symbol? n) n
          (vec (map #(if (instance? exp.env.FactoredState %) (dissoc (exp.env/as-map %) :const) %) n)))))

  (defmethod print-method ::SimpleNode [x s]
    (print-method (str "Nd<" (name-str x) "," (:reward x) "," (:goal? x) ">") s)))

(declare make-cpc-node)

(deftype CAC-Node [name gap in-clause action out-clause reward-bounds] :as this
  Comparable    (compareTo  [x] (compare-saha-nodes this x))
  is/Summary    (max-reward [] (nth reward-bounds 1))   
  is/Node       (node-name  [] name)
                (node-goal? [] (neg? gap))
  PSAHA-Summary (min-reward [] (nth reward-bounds 0))
                (max-gap    [] gap))

(defn make-cac-node [in-clause action out-clause reward-bounds]
  (CAC-Node
   [::CAC in-clause (env/action-name action) out-clause]
   (if (or (env/primitive? action) (not (hierarchy/can-refine? action in-clause)))
       is/neg-inf
       (- (nth reward-bounds 1) (nth reward-bounds 0)))
   in-clause action out-clause reward-bounds))

(defn make-root-cac-node [in-clause action]
  (let [[out-clause reward-bounds] (hierarchy/next-clause-and-rewards action in-clause)]
    (make-cac-node in-clause action out-clause reward-bounds)))

(defn cac-node-refinements [cac]
  (let [{:keys [in-clause action out-clause reward-bounds gap]} cac]
    (assert (not (neg? gap)))
    (for [[constraint ref] (hierarchy/immediate-refinements-clause action in-clause)
          :let             [constrained-clause (hierarchy/restrict-clause in-clause constraint)]
          :when            constrained-clause]
      [constraint (make-cpc-node constrained-clause ref out-clause [is/ninf (nth reward-bounds 1)])])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CPC Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: no summary?
 ; TODO. ..

(deftype CPC-Node [name gap in-clause plan out-clause reward-bounds] :as this
  Comparable    (compareTo  [x] (compare-saha-nodes this x))
  is/Summary    (max-reward [] (nth reward-bounds 1))   
  is/Node       (node-name  [] name)
                (node-goal? [] (neg? gap))
  PSAHA-Summary (min-reward [] (nth reward-bounds 0))
                (max-gap    [] gap))

(defn make-cpc-node [in-clause plan out-clause reward-bounds]
  (CAC-Node
   [::CPC in-clause (map env/action-name plan) out-clause]
   
   in-clause action out-clause reward-bounds))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searches ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Idea is similar to saha-simple.  Two main differences:
; 1.  To support clauses, we have to be able to dynamiaclly split.  Eventually, this 
;    should be done by dynamicsally wrapping old nodes.  For now, wej ust use caching.
; 2.  Since we're only allowing a single output clause per action, we don't need the weird
;    inner/outer cache deal.  

; ;Need to add cacpc node.  Initial one comes deterministically from cpc.  
; Then, recipe for AND-search:
 ; Simplest recipe: Whenever we get a goal, make a new cpcpc node and start over.
  ;  This will give big ugly chains for every primitive solution, however.
  ; Note: once we start getting results for one clause-output side, we probably don't want to 
    ; refine other side again?
  ; Note; for each half of cpcpc, we know in advance if it's clause-output or state-output. 

; Requirement: only get primitive goals for primitive ends (i.e, minimal state abstraction?) ?

;; TODO: note we can't copy searches.  Everything should go through nodes.  This may present a problem?

; Every node is CACACACACAC.  

; CAC has OR-search
 ; Can be of two types: 
  ; top-down:
   ; Initially with angelic bound
   ; Then over refinements, which are CPC=CACPC
  ; bottom-up for CAC' (parent CAC part of identity):
   ; start with nothing, fill with things as we go (respecting consistency, hopefully)
   ; max-reward also defers to parent CAC, should make sure we don't get too eager.?
   ;   Except, we can't actually go to parent through this node.
   ;    Can set gap to neg-inf when we get val through parent
   ;     But then how do we get informed when things added bottom-up ??
   ;    So, we're essentially back at same consistency problem?  
   ;    Solution: just drive parent (*through different cache* until cost increase).
   ;              (keep only relevant goal nodes).
   ;    Not beautiful, but solves problems. 
 ; Can return two types of goals:
  ; CAC' for refined C, partially populated bottom-up
  ; Primitive plan, iff both ends concrete?
 ; If it gets 
  ; primitive goal from below, just passes through.
  ; refined CAC'PC from below, just researchify (CAC' should not be recreated, ideally C'PC is wrapped).
  ; refined CACPC' from below, 
   ; Create and return fresh CAC' bottom-up node, or add to it if node already exists.

; CPC has AND-search
 ; Initially over basic decomposition.
 ; Can return two types of goals:
  ; CPC' for refined C
  ; Primitive plan, iff both ends concrete?
 ; If it gets:
  ; Primitive goal from below (1), depends on (2)
  ; Primitive goal form below (2), act like SAHA-simple.
  ;   (must get primitive goal from (1), or eventually stall?)
  ; Refined goal from below (1), 
  ;   Return CAC'PC upwards, stop refining (2) ?
  ; Retined goal from below (2),
  ;   Return CACPC' upwards, stop refining (1) ?
  ; Issue with these: different stopping for different refs may reduce caching.
; Can possibly tweak/simplify this slightly by returning new node immediately on primitive sol, sub in sol
 ; Then, nodes have primitive prefix & suffix as well, handled/removed somehow in CAC searchify.  

; Only issue here: CAC children may multiply over intermediate trajectories.
; Could try to do something fancy.  Better, just factor hierarchy; nothing lost if all refs <= 2 count.

; i.e., CAC is generalized-goal search!1!!!


;; TODO: need gap in refinement criteria ? Otherwise, may refine stupid thing if thing we wanted already refined.


(declare get-saha-cpc-search)

;; TODO: where do we use opt desc ??  Should we cache nodes as well as searches ? 
 ; Or cache searches in nodes, or what ? 
(defn get-saha-cac-search [cac-node]
  (is/get-cached-search *problem-cache* (node-name cac-node)
    (is/make-recursive-sr-search cac-node cac-refinements get-saha-cpc-search)))

(defn get-saha-cpc-search [cpc-node]
  (is/get-cached-search *problem-cache* (node-name cpc-node)
    (let [[cac-node rest-cpc-node] (cpc-split cpc-node)]
      (is/make-and-search cpc-node
        (get-saha-cac-search cac-node)
        (get-saha-cpc-search cpc-node)
        (fn [s1 s2] (if (>= (max-gap s1) (max-gap s2)) s1 s2))
        add-saha-summaries
        (fn goal-fn [g1 g2]
          .....  ; (two cases: new outcome, actual goal)
          ))))
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