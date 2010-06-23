(ns exp.hierarchical-incremental-search
  (:require [edu.berkeley.ai.util :as util]
            [exp.env :as env] 
            [exp.hierarchy :as hierarchy]
            [exp.incremental-search :as is])
  (:import  [java.util HashMap]))


; Angelic hierarchy of optimal incremental searches

;; TODO: fix paredit key bindings.
;; TODO: formap 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def #^HashMap *problem-cache* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchical Forward State ;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype HierarchicalForwardState [state reward opt-sol remaining-actions])

(defn hfs-name 
  ([hfs] [(:state hfs) (map env/action-name (:remaining-actions hfs))])
  ([hfs more-name] (conj (hfs-name hfs) more-name)))

(defn make-root-hfs [state action]
  (HierarchicalForwardState state 0 [] [action]))

(defn hfs-children [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (when-let [[f & r] (seq remaining-actions)]      
      (if (env/primitive? f)
        (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
          [(HierarchicalForwardState ss (+ reward sr) (conj opt-sol f) r)]) 
        (for [ref (hierarchy/immediate-refinements f state)]
          (HierarchicalForwardState state reward opt-sol (concat ref r)))))))

(defn combine-hfs [n1 n2 state-combiner action-combiner]
  (HierarchicalForwardState
   (state-combiner       (:state n1)   (:state n2))
   (+                    (:reward n1)  (:reward n2))
   (into                 (:opt-sol n1) (:opt-sol n2))
   (action-combiner      (:remaining-actions n1) (:remaining-actions n2))))

;; Sub and lift -- used by recursive, inverted, saha (drop only)
(defn hfs-first-sub-name "Name for first abstracted subproblem of hfs" [hfs]
  (let [{[f] :remaining-actions state :state} hfs]      
    [(env/extract-context state (env/precondition-context f state)) (env/action-name f)]))

(defn hfs-first-sub "First abstracted subproblem of hfs" [hfs]
  (let [{[f] :remaining-actions state :state} hfs]
    (make-root-hfs (env/get-logger state (env/precondition-context f state)) f)))

(defn lift-hfs "Lift child-solution into the context of parent-node, counterpart to sub."
  [parent child] 
  (combine-hfs parent child env/transfer-effects
               (fn [r1 r2] (util/assert-is (empty? r2)) (next r1))))


;; Used for inverted only
(defn adjust-hfs-reward [h r]
  (HierarchicalForwardState (:state h) (+ r (:reward h)) (:opt-sol h) (:remaining-actions h)))

; used for saha only
(defn first-action-hfs "Return hfs for just first action." [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (HierarchicalForwardState state 0 nil (take 1 remaining-actions))))

(defn rest-actions-hfs "Return hfs for just first action." [hfs mid-state]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (HierarchicalForwardState mid-state 0 nil (drop 1 remaining-actions))))

(defn join-hfs [first-result rest-result final-state]
  (combine-hfs first-result rest-result (constantly final-state) (constantly nil)))



(defn hfs-can-reach? [hfs s]
  (or (seq (:remaining-actions hfs)) (= s (:state hfs))))

(defn hfs-cycle-level [hfs]
  (when-let [a (first (:remaining-actions hfs))] (hierarchy/cycle-level a (:state hfs))))

(defn hfs-gg "Return gg-hfs and goal-map, or nil if not gg." [hfs]
  (let [a (util/safe-singleton (:remaining-actions hfs))]
    (when-let [[gga goal-map] (hierarchy/gg-action a)]
      [(HierarchicalForwardState (:state hfs) (:reward hfs) (:opt-sol hfs) [gga])
       goal-map
       (every? (env/precondition-context a (:state hfs)) (keys goal-map))])))

(defn hfs-optimistic-map [hfs]
  (let [{:keys [state remaining-actions]} hfs]
    (assert (util/singleton? remaining-actions))
    (env/optimistic-map (first remaining-actions) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HFS & Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn hfs->simple-node 
  ([hfs] (is/SimpleNode (hfs-name hfs) (:reward hfs) (empty? (:remaining-actions hfs)) hfs))
  ([hfs extra-data] (hfs->simple-node hfs extra-data (empty? (:remaining-actions hfs))))
  ([hfs extra-data goal?] ; for inverted, needs non-goal goal-looking nodes.
     (is/SimpleNode (conj (hfs-name hfs) extra-data) (:reward hfs) goal? [hfs extra-data]))
  ([hfs extra-data goal? rew] ; for saha, needs estimated reward.
     (is/SimpleNode (conj (hfs-name hfs) extra-data) rew goal? [hfs extra-data])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searches ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Basic idea behind heterogenous search: 
;   We can generate expansions for nodes in different ways.
;   Always assume we have an HFS within a recursive ID.  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn expand-hfs [hfs] (map hfs->simple-node (hfs-children hfs)))

(defn make-fast-flat-search [root-hfs]
  (is/make-flat-incremental-dijkstra (hfs->simple-node root-hfs) (comp expand-hfs :data)))

(defn make-flat-search  [root-hfs]
  (is/make-recursive-incremental-dijkstra (hfs->simple-node root-hfs) (comp expand-hfs :data)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-abstract-subsearch [hfs search-factory]    
  (is/WrappedSubSearch 
   (is/get-cached-search *problem-cache* (hfs-first-sub-name hfs)
     (search-factory (hfs-first-sub hfs))) 
   (:reward hfs) 
   #(is/offset-simple-summary % (:reward hfs))
   #(->> % :data (lift-hfs hfs) hfs->simple-node)))

(defn make-recursive-ef-search [hfs searchify-hfs-fn]
  (is/make-recursive-sr-search (hfs->simple-node hfs) 
      #(expand-hfs (:data %)) #(searchify-hfs-fn (:data %))))

(defn recursive-abstract-subsearch 
  ([hfs] (recursive-abstract-subsearch hfs recursive-abstract-subsearch))
  ([hfs searchify-fn] 
     (make-abstract-subsearch hfs #(make-recursive-ef-search % searchify-fn))))

(defn make-recursive-search [root-hfs] (:search (recursive-abstract-subsearch root-hfs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hybrid flat/rec search ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-acyclic-searchify [root-hfs]
  (let [root-cycle-level (hfs-cycle-level root-hfs)]
    #(if (and root-cycle-level (= (hfs-cycle-level %) root-cycle-level))
        (expand-hfs %)
      (recursive-abstract-subsearch % (make-acyclic-searchify %)))))

(defn make-acyclic-recursive-search [root-hfs] 
  (:search (recursive-abstract-subsearch root-hfs (make-acyclic-searchify root-hfs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hybrid gg/rec search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Search that takes advantage of generalized-goal HLAs as defined by the "hierarchy/gg-*" iface.
; Assume top-level action is never GG .  ?
;; In a sense, a counterpart to simple, which shares across init states but not goals.

;; TODO: definitely want to be able to switch out of gg mode?
(declare abstract-gg-search)
(defn gg-search [hfs]   
;  (println hfs (hfs->simple-node hfs))
  (if-let [[gg-hfs goal-map single-goal?] (hfs-gg hfs)]
    (let [goal-vars (keys goal-map)]
      (is/get-generalized-search *problem-cache* (hfs-first-sub-name gg-hfs)     
        (fn [n] (let [s (:state (:data n))] (map #(env/get-var s %) goal-vars)))
        (map goal-map goal-vars) single-goal?
        (make-fast-flat-search gg-hfs)))
    (make-recursive-ef-search hfs abstract-gg-search)))

(defn abstract-gg-search [hfs] (make-abstract-subsearch hfs gg-search))

(defn make-gg-search [root-hfs] (:search (abstract-gg-search root-hfs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Inverted ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: Rewards passed around are all global-best.

;; TODO: think about IDA* 
;; TODO: partial expansions for goals ? 

; TODO: goal generalization.

(declare make-upward-node make-inverted-node)

; parents are [parent-hfs parent-ic] pairs. base-reward is that of first parent.
(deftype InvertedCache [results-atom parents-atom base-reward])

(defn add-cache-result [_ [hfs ic :as hfs-ic-pair]]
  (let [{:keys [results-atom parents-atom base-reward]} ic]
    (when-let [o (peek @results-atom)] (util/assert-is (<= (:reward hfs) (:reward o))))
    (swap! results-atom conj hfs)
    (map #(make-upward-node % hfs base-reward) @parents-atom)))

(defn add-cache-parent [#^HashMap cc [parent-hfs parent-ic :as parent-pair]]
  (let [ic (util/cache-with cc (hfs-first-sub-name parent-hfs) 
             (InvertedCache (atom []) (atom []) (:reward parent-hfs)))
        {:keys [results-atom parents-atom base-reward]} ic]
    (when-let [o (last @parents-atom)] 
      (util/assert-is (<= (:reward parent-hfs) (:reward (first o)))))
    (swap! parents-atom conj parent-pair)
    (if (= (count @parents-atom) 1)
      (map #(make-inverted-node % ic) 
           (hfs-children (adjust-hfs-reward (hfs-first-sub parent-hfs) base-reward)))
      (map #(make-upward-node parent-pair % base-reward) @results-atom))))

(defn make-inverted-node [hfs parent-ic] (hfs->simple-node hfs parent-ic false))

(defn make-upward-node [[hfs ic] child-hfs base-reward]
  (let [lifted (adjust-hfs-reward (lift-hfs hfs child-hfs) (- base-reward))]
    (if ic (make-inverted-node lifted ic) (hfs->simple-node lifted))))

(defn make-inverted-expand-fn [cc]
  (fn [{hfs-ic-pair :data}] 
    ((if (seq (:remaining-actions (first hfs-ic-pair))) add-cache-parent add-cache-result) 
     cc hfs-ic-pair)))

(defn make-inverted-search [root-hfs]
  (is/make-flat-incremental-dijkstra 
   (make-inverted-node root-hfs nil) 
   (make-inverted-expand-fn (HashMap.))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare get-saha-sps-search)


(defn get-sas-map "Get a map from outer final states to SAS nodes/" [hfs]
  (util/cache-with *problem-cache* (hfs-name hfs) ; unabstracted state SA cache
    (util/map-keys #(env/transfer-effects (:state hfs) %)
      (util/cache-with *problem-cache* (hfs-first-sub-name hfs) ; abstracted state SA cache
        (let [inner-hfs (hfs-first-sub hfs)
              next-hfs (lazy-seq (hfs-children inner-hfs))]
          (into {}
                (for [[ss sr] (hfs-optimistic-map inner-hfs)]
                  [ss  (is/cache-incremental-search
                        (is/make-recursive-sr-search 
                         (hfs->simple-node inner-hfs ss false sr)
                         (fn [_] (for [n next-hfs :when (hfs-can-reach? n ss)] 
                                   (hfs->simple-node n ss)))
                         #(apply get-saha-sps-search (:data %))))])))))))

(defn get-saha-sas-search [hfs final-state] 
  (((get-sas-map hfs) final-state)))


;; TODO: remove expensive names.
(defn get-saha-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (util/make-safe (seq (:remaining-actions hfs)))]
    (if (util/singleton? r-a)
      (get-saha-sas-search hfs final-state)
      (is/get-cached-search *problem-cache* (hfs-name hfs final-state)
        (let [outer-cache (get-sas-map (first-action-hfs hfs))]
          (is/make-recursive-sr-search (hfs->simple-node hfs [::F final-state])
           (fn [_] (map #(hfs->simple-node hfs %) (keys outer-cache)))
           (fn [n] 
             (let [ss (second (:data n))]
               (is/make-and-search n
                 ((outer-cache ss)) 
                 (get-saha-sps-search (rest-actions-hfs hfs ss) final-state)                
                 (fn [x y] x)
                 is/add-simple-summaries 
                 (fn [g1 g2] 
                   (hfs->simple-node (join-hfs (first (:data g1)) (first (:data g2)) final-state) 
                                     :goal)))))))))))


(defn make-saha-search [root-hfs]
  (get-saha-sas-search root-hfs (util/safe-singleton (keys (hfs-optimistic-map root-hfs)))))

;; TODO: version with better meta-level control, PN-style. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)

(defn hierarchical-search 
  ([henv policy search-maker] (hierarchical-search henv policy search-maker identity))
  ([henv policy search-maker hfs-sol-extractor]
     (binding [*node-type-policy* policy
               *problem-cache*    (HashMap.)]
       (let [e    (hierarchy/env henv)
             init (env/initial-logging-state e)
             tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
             top  (search-maker (make-root-hfs init tla))]
         (when-let [sol (is/first-goal-node top)]
           (let [sol-hfs (hfs-sol-extractor (:data sol))]
             [(:opt-sol sol-hfs) (:reward sol-hfs)]))))))



(defn sahucs-fast-flat [henv]
  (hierarchical-search henv nil make-fast-flat-search))

(defn sahucs-flat [henv]
  (hierarchical-search henv nil make-flat-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv nil make-recursive-search))

(defn sahucs-dijkstra [henv]
  (hierarchical-search henv nil make-acyclic-recursive-search))

(defn sahucs-gg [henv]
  (hierarchical-search henv nil make-gg-search))

(defn sahucs-inverted [henv]
  (hierarchical-search henv nil make-inverted-search))

(defn saha-simple [henv]
  (hierarchical-search henv nil make-saha-search first))



(comment
  (do (use '[exp env hierarchy taxi ucs hierarchical-incremental-search] 'edu.berkeley.ai.util) (require '[exp sahucs-simple sahucs-simple-dijkstra sahucs-inverted saha-simple] '[exp.old ahois]))
   (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
    (doseq [alg `[sahucs-flat sahucs-fast-flat exp.sahucs-simple/sahucs-simple sahucs-simple exp.sahucs-simple-dijkstra/sahucs-simple-dijkstra sahucs-dijkstra exp.sahucs-inverted/sahucs-inverted sahucs-inverted exp.saha-simple/saha-simple saha-simple ]]
      (time (println alg (run-counted #(debug 0 (second ((resolve alg) h)))))))))