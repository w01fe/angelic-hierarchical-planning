(ns angelic.search.incremental.implicit
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env] 
            [angelic.hierarchy :as hierarchy]
            [angelic.incremental-search :as is]
            [angelic.hierarchical-incremental-search :as his])
  (:import  [java.util HashMap]))


; Hierarchical algorithms that can use angelic valuations.
; Included are algorithms for explicit valuations, as well as implicit set-vased ones. 

; (require optimistic & pessimistic in line, by single map from clauses to [p o] pairs) ?
; Still have correspondence problem.
; unless: require single "region"/clause.  All existing hierarchies had this anyway ?  

; nil is a valid clause, meaning "empty" ?
; States can be used as-is with these functions? 
(declare hierarchy/clause-is-state?) ;; Clause is also a state
(declare hierarchy/can-refine-from-clause?) ; Is clause concrete enough to meaningfully refine this action?
(declare hierarchy/immediate-refinements-clause) ; Returns seq of [constraint ref] pairs from this clause.
(declare hierarchy/next-clause-and-rewards) ; takes action & clause, returns [result-clause [pess-rew opt-rew]]
(declare hierarchy/restrict-clause) ;; Takes clause & constraint; returns nil for invalid.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;; Angelic Hierarchical State ;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype AngelicHierarchicalState [in-clause actions reward-bounds out-clause primitive?])

(defn ahs-name 
  ([ahs] [(:in-clause ahs) (map env/action-name actions) (:out-clause ahs)])
  ([ahs more-name] (conj (ahs-name ahs) more-name)))

(defn ahs-solution-pair [ahs]
  (when ahs
   (assert (:primitive? ahs))
   (assert (apply = (:reward-bounds ahs)))
   [(:actions ahs) (first (:reward-bounds ahs))]))

(defn make-root-ahs [in action out]
  (AngelicHierarchicalState state 0 [] [action]))

(defn ahs-children [ahs]
  (let [{:keys [state reward opt-sol remaining-actions]} ahs]
    (when-let [[f & r] (seq remaining-actions)]      
      (if (env/primitive? f)
        (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
          [(AngelicHierarchicalState ss (+ reward sr) (conj opt-sol f) r)]) 
        (for [ref (hierarchy/immediate-refinements f state)]
          (AngelicHierarchicalState state reward opt-sol (concat ref r)))))))

(defn combine-ahs [n1 n2 state-combiner action-combiner]
  (AngelicHierarchicalState
   (state-combiner       (:state n1)   (:state n2))
   (+                    (:reward n1)  (:reward n2))
   (into                 (:opt-sol n1) (:opt-sol n2))
   (action-combiner      (:remaining-actions n1) (:remaining-actions n2))))

;; Sub and lift -- used by recursive, inverted, saha (drop only)
(defn ahs-first-sub-name "Name for first abstracted subproblem of ahs" [ahs]
  (let [{[f] :remaining-actions state :state} ahs]
    [(if *state-abstraction?* (state/extract-context state (env/precondition-context f state)) state) 
     (env/action-name f)]))

(defn ahs-first-sub "First abstracted subproblem of ahs" [ahs]
  (let [{[f] :remaining-actions state :state} ahs]
    (make-root-ahs (env/get-logger state (if *state-abstraction?* (env/precondition-context f state) *full-context*)) f)))

(defn lift-ahs "Lift child-solution into the context of parent-node, counterpart to sub."
  [parent child] 
  (combine-ahs parent child env/transfer-effects
               (fn [r1 r2] (util/assert-is (empty? r2)) (next r1))))


;; Used for inverted only
(defn adjust-ahs-reward [h r]
  (AngelicHierarchicalState (:state h) (+ r (:reward h)) (:opt-sol h) (:remaining-actions h)))

; used for saha only
(defn first-action-ahs "Return ahs for just first action." [ahs]
  (let [{:keys [state reward opt-sol remaining-actions]} ahs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (AngelicHierarchicalState state 0 nil (take 1 remaining-actions))))

(defn rest-actions-ahs "Return ahs for just first action." [ahs mid-state]
  (let [{:keys [state reward opt-sol remaining-actions]} ahs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (AngelicHierarchicalState mid-state 0 nil (drop 1 remaining-actions))))

;; TODO: remove expensive assertino.
(defn join-ahs [parent-ahs first-result rest-result final-state]
  (combine-ahs first-result rest-result (constantly final-state) (constantly nil))
#_  (let [my-final (reduce env/transfer-effects (:state parent-ahs)
                         [(:state first-result) (:state rest-result)])]
    (util/assert-is (= (dissoc (state/as-map final-state) :const) 
                       (dissoc (state/as-map my-final) :const)))
    (combine-ahs first-result rest-result (constantly my-final) (constantly nil))))



(defn ahs-can-reach? [ahs s]
  (or (seq (:remaining-actions ahs)) (= s (:state ahs))))

(defn ahs-cycle-level [ahs]
  (when-let [a (first (:remaining-actions ahs))] (hierarchy/cycle-level a (:state ahs))))

(defn ahs-gg "Return gg-ahs and goal-map, or nil if not gg." [ahs]
  (let [a (util/safe-singleton (:remaining-actions ahs))]
    (when-let [[gga goal-map] (hierarchy/gg-action a)]
      [(AngelicHierarchicalState (:state ahs) (:reward ahs) (:opt-sol ahs) [gga])
       goal-map
       (every? (env/precondition-context a (:state ahs)) (keys goal-map))])))

(defn ahs-optimistic-map [ahs]
  (let [{:keys [state remaining-actions]} ahs]
#_    (apply println "Optimistic map for " (ahs-first-sub-name ahs) "is\n"
             (for [[s r] (hierarchy/optimistic-map (util/safe-singleton remaining-actions) state)]
               (str "  " (env/extract-effects s) ": " r "\n")))
    (hierarchy/optimistic-map (util/safe-singleton remaining-actions) state)))


;;;;;;;;;;;;;;;;;;;;;;;; Simple Weighted Summary & Node ;;;;;;;;;;;;;;;;;;;;;;;;
;;; lifted from explicit-...


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


(defn add-sw-summaries [s1 s2]
  (let [rew (+ (is/max-reward s1) (is/max-reward s2))]
    (if (= rew is/neg-inf) worst-sw-summary   
        (SWSummary rew (+ (pess-reward s1) (pess-reward s2)) (max (max-gap s1) (max-gap s2))))))


;; Idea was: why have generic nodes, and then code that uses generic fields 
; in special way, plus separate "angelic hierarchical state".  
; Why not just bake logic into different node types? 
; that might make things slightly more clear, but leads to lots of dup effort,
; may make, e..g, other weighted versions more difficult.  


(defn compare-saha-nodes [x1 x2]
  (let [c (compare-saha-summaries x1 x2)]
    (if (zero? c)  
        (compare (and (instance? angelic.search.incremental.Node x2) (is/node-goal? x2))
                 (and (instance? angelic.search.incremental.Node x1) (is/node-goal? x1)))
        c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CAC Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(comment 
  (defn name-str [x]
    (let [n (:name x)]
      (if (symbol? n) n
          (vec (map #(if (instance? angelic.env.FactoredState %) (dissoc (angelic.state/as-map %) :const) %) n)))))

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



