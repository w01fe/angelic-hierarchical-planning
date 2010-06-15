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

;; Drop and lift -- used by recursive, inverted, saha (drop only)
(defn drop-hfs
  "Construct first abstracted name & fn returning hfs subproblem, counterpart to lift."
  [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs
        [f & r] remaining-actions
        context (env/precondition-context f state)]      
    [[(env/extract-context state context) (env/action-name f)]
     #(make-root-hfs (env/get-logger state context) f)]))

(defn lift-hfs "Lift child-solution into the context of parent-node, counterpart to drop."
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

(defn hfs-optimistic-map [hfs]
  (let [{:keys [state remaining-actions]} hfs]
    (assert (util/singleton? remaining-actions))
    (env/optimistic-map (first remaining-actions) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HFS & Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn hfs->simple-node 
  ([hfs] (is/SimpleNode (hfs-name hfs) (:reward hfs) (empty? (:remaining-actions hfs)) hfs))
  ([hfs extra-data] (is/SimpleNode (conj (hfs-name hfs) extra-data) (:reward hfs) 
                                   (empty? (:remaining-actions hfs)) [hfs extra-data])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Searches ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn hfs-simple-children [hfs] (map hfs->simple-node (hfs-children hfs)))

(defn make-fast-flat-search [root-hfs]
  (is/make-flat-incremental-dijkstra (hfs->simple-node root-hfs) hfs-simple-children))

(defn make-flat-search  [root-hfs]
  (is/make-recursive-incremental-dijkstra (hfs->simple-node root-hfs) hfs-simple-children))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: recursive recursively is where polymorphism fits in.

(declare make-recursive-search)

(defn make-abstracted-subgoal-search [hfs]    
  (is/WrappedSubSearch 
   (let [[name abstract-hfs-fn] (drop-hfs hfs)]
     (is/get-cached-search *problem-cache* name
       (let [dropped (abstract-hfs-fn)]
         (make-recursive-ef-search (hfs->simple-node dropped) (hfs-simple-children dropped)
                                   #(make-abstracted-subgoal-search (:data %)))))) 
   (:reward hfs) 
   #(is/offset-simple-summary % (:reward hfs))
   #(->> % :data (lift-hfs hfs) hfs->simple-node)))

(defn make-recursive-ef-search "Expand once, then searchify." [root-node first-children searchify-fn]
  (is/make-recursive-incremental-dijkstra root-node 
    #(if (identical? root-node %) first-children (searchify-fn %))))

(defn make-recursive-search [root-hfs] (:search (make-abstracted-subgoal-search root-hfs)))


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
  (let [[name abstract-hfs-fn] (drop-hfs parent-hfs)
        ic (util/cache-with cc name (InvertedCache (atom []) (atom []) (:reward parent-hfs)))
        {:keys [results-atom parents-atom base-reward]} ic]
    (when-let [o (last @parents-atom)] (util/assert-is (<= (:reward parent-hfs) (:reward (first o)))))
    (swap! parents-atom conj parent-pair)
    (if (= (count @parents-atom) 1)
      (map #(make-inverted-node % ic) (hfs-children (adjust-hfs-reward (abstract-hfs-fn) base-reward)))
      (map #(make-upward-node parent-pair % base-reward) @results-atom))))

(defn make-inverted-node [hfs parent-ic] (hfs->simple-node hfs parent-ic))

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

;; TODO: smarter about failed searches... ?
(defn get-inner-sa-cache "Get a map from inner final states to SAS nodes."[hfs]
  (let [[name abstract-hfs-fn] (drop-hfs hfs)]
    (util/cache-with *problem-cache* name
      (let [inner-hfs (abstract-hfs-fn)
            next-hfs (lazy-seq (hfs-children inner-hfs))]
        (into {}
          (for [[ss sr] (hfs-optimistic-map inner-hfs)]
            [ss (is/cache-incremental-search
                 (make-recursive-ef-search 
                  (hfs->simple-node inner-hfs ss)
                  (lazy-seq (for [n next-hfs :when (hfs-can-reach? n ss)] (hfs->simple-node n ss)))
                  #(get-saha-sps-search (:data %) ss)))]))))))

(defn get-outer-sa-cache "Get a map from outer final states to SAS nodes/" [hfs]
  (util/cache-with *problem-cache* (hfs-name hfs)
    (util/map-keys #(env/transfer-effects (:state hfs) %) (get-inner-sa-cache hfs))))

(defn get-saha-sas-search [hfs final-state] 
  ((force ((get-outer-sa-cache hfs) final-state))))


;; TODO: remove expensive names.
(defn get-saha-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (:remaining-actions hfs)]
    (assert (seq r-a))
    (if (util/singleton? r-a)
      (get-saha-sas-search hfs final-state)
      (is/get-cached-search *problem-cache* (hfs-name hfs final-state)
        (let [outer-cache (get-outer-sa-cache (first-action-hfs hfs))]
          (make-recursive-ef-search (hfs->simple-node hfs [::F final-state])
           (map #(hfs->simple-node hfs %) (keys outer-cache))
           (fn [n] (is/make-and-search n
                    ((outer-cache (:data n))) 
                    (get-saha-sps-search (rest-actions-hfs hfs (:data n)) final-state)                
                    (fn [x y] x)
                    is/add-simple-summaries 
                    #(hfs->simple-node (join-hfs (:data %1) (:data %2) final-state))))))))))


(defn make-saha-search [root-hfs]
  (get-saha-sas-search root-hfs (util/safe-singleton (keys (hfs-optimistic-map root-hfs)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *node-type-policy*)

(defn hierarchical-search [henv policy search-maker]
  (binding [*node-type-policy* policy
            *problem-cache*    (HashMap.)]
    (let [e    (hierarchy/env henv)
          init (env/initial-logging-state e)
          tla  (hierarchy/TopLevelAction e [(hierarchy/initial-plan henv)])
          top  (search-maker (make-root-hfs init tla))]
      (when-let [sol (is/first-goal-node top)]
        [(:opt-sol (:data sol)) (:reward (:data sol))]))))



(defn sahucs-fast-flat [henv]
  (hierarchical-search henv nil make-fast-flat-search))

(defn sahucs-flat [henv]
  (hierarchical-search henv nil make-flat-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv nil make-recursive-search))

(defn sahucs-inverted [henv]
  (hierarchical-search henv nil make-inverted-search))

(defn saha-simple [henv]
  (hierarchical-search henv nil make-saha-search))



