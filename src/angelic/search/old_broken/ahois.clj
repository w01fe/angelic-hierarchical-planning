(ns angelic.old.ahois
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env] 
            [angelic.hierarchy :as hierarchy]
            [angelic.old.incremental-search :as is])
  (:import  [java.util HashMap]))


; Angelic hierarchy of optimal incremental searches

;; TODO: fix paredit key bindings.
;; TODO: formap 

;; TODO: generalized search


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Forward Search Node ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This should probably live in another file -- just here as an example.

(defn make-forward-search-node [actions-fn goal-fn state reward opt-sol]
  (is/SimpleNode state reward (if (goal-fn state) opt-sol)       
    (lazy-seq
     (for [a (actions-fn state)
           :when (env/applicable? a state)
           :let  [[ss r] (env/successor a state)]]
       (make-forward-search-node actions-fn goal-fn ss (+ reward r) (conj opt-sol a))))
    nil))

(defn make-forward-search-root-node [env]
  (make-forward-search-node (env/actions-fn env) (env/goal-fn env) (env/initial-state env) 0 []))

(defn make-forward-search [env] (is/make-flat-incremental-dijkstra (make-forward-search-root-node env)))

(defn uniform-cost-search [env] (is/first-solution-reward-pair (make-forward-search env)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchical ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype HierarchicalForwardState [state reward opt-sol remaining-actions])

(defn hfs-name [hfs]
  [(:state hfs) (map env/action-name (:remaining-actions hfs))])

(defn make-root-hfs [state action]
  (HierarchicalForwardState state 0 [] [action]))

(defn hfs-children [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs
        [f & r] remaining-actions]      
    (if (env/primitive? f)
      (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
        [(HierarchicalForwardState ss (+ reward sr) (conj opt-sol f) r)]) 
      (for [ref (hierarchy/immediate-refinements f state)]
        (HierarchicalForwardState state reward opt-sol (concat ref r))))))

(defn hfs->simple-node [hfs]
  (if (empty? (:remaining-actions hfs))
    (is/SimpleNode (hfs-name hfs) (:reward hfs) (:opt-sol hfs) nil hfs)
    (is/SimpleNode (hfs-name hfs) (:reward hfs) nil 
                   (lazy-seq (map hfs->simple-node (hfs-children hfs))) hfs)))

(defn lift-state [parent child] (state/apply-effects parent (env/extract-effects child)))

(defn lift-hfs 
  "Lift child-solution into the context of parent-node."
  [parent child-solution]
  (assert (:opt-sol child-solution))
  (HierarchicalForwardState
   (lift-state        (:state parent)   (:state child-solution))
   (+                 (:reward parent)  (:reward child-solution))
   (concat            (:opt-sol parent) (:opt-sol child-solution))
   (next (:remaining-actions parent))))

(defn adjust-hfs-reward [h r]
  (HierarchicalForwardState (:state h) (+ r (:reward h)) (:opt-sol h) (:remaining-actions h)))


(defn drop-hfs
  "Construct first abstracted name & fn returning hfs subproblem, counterpart to lift."
  [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs
        [f & r] remaining-actions
        context (env/precondition-context f state)]      
    [[(state/extract-context state context) (env/action-name f)]
     #(make-root-hfs (env/get-logger state context) f)]))

(defn first-action-hfs "Return hfs for just first action." [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (HierarchicalForwardState state 0 nil (take 1 remaining-actions))))

(defn rest-actions-hfs "Return hfs for just first action." [hfs mid-state]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (HierarchicalForwardState mid-state 0 nil (drop 1 remaining-actions))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here, solution are solutions, and we break apart the hfs each time.

(defn make-simple-flat-search [state action]
  (is/make-flat-incremental-dijkstra (hfs->simple-node (make-root-hfs state action))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Flat search2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; slower, using recursive search doodad.  If we allowed searchify to return list of nodes,
; could avoid nonsense here.

; Nonsense is: to expand node, we create a search whose goals are its flat refinements.
; To lift these, we just extract the goals.

; Now, where do we put switching logic?  Can (1) put it in node construction, or (2) in searchify.

;(defn make-expanding-node )

(defn expanding-searchify [n]
  [(is/make-flat-incremental-dijkstra 
    (is/SimpleNode (gensym) 0 nil (map is/make-meta-goal-node (is/expand n)) nil)) 
   0 is/solution])

(defn make-flat-search  [state action]
  (is/make-recursive-incremental-dijkstra
   (hfs->simple-node (make-root-hfs state action)) 
   expanding-searchify))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Recursive search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: recursive recursively is where polymorphism fits in.
 
(def #^HashMap *problem-cache* nil)
(defn recursively-searchify-hfs [hfs]
  (let [[name abstract-hfs-fn] (drop-hfs hfs)]
    [(is/get-cached-search *problem-cache* name
       (is/make-recursive-incremental-dijkstra
        (hfs->simple-node (abstract-hfs-fn)) 
        (comp recursively-searchify-hfs :data)))
     (:reward hfs)
     #(->> % :data (lift-hfs hfs) hfs->simple-node)]))

(defn make-recursive-search [state action]
  (first (recursively-searchify-hfs (make-root-hfs state action))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Inverted ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: Rewards passed around are all global-best.

;; TODO: think about IDA* 
;; TODO: partial expansions for goals ? 

; TODO: goal generalization.

(declare make-upward-node make-inverted-node)

; parents are [parent-hfs parent-ic] pairs. base-reward is that of first parent.
(deftype InvertedCache [results-atom parents-atom base-reward])

(defn add-cache-result [cc [hfs ic :as hfs-ic-pair]]
  (let [{:keys [results-atom parents-atom base-reward]} ic]
;    (when-let [o (peek @results-atom)] (util/assert-is (<= (:reward hfs) (:reward o))))
    (swap! results-atom conj hfs)
    (map #(make-upward-node cc % hfs base-reward) @parents-atom)))

(defn add-cache-parent [#^HashMap cc [parent-hfs parent-ic :as parent-pair]]
  (let [[name abstract-hfs-fn] (drop-hfs parent-hfs)
        ic (util/cache-with cc name (InvertedCache (atom []) (atom []) (:reward parent-hfs)))
        {:keys [results-atom parents-atom base-reward]} ic]
;    (when-let [o (last @parents-atom)] (util/assert-is (<= (:reward parent-hfs) (:reward (first o)))))
    (swap! parents-atom conj parent-pair)
    (if (= (count @parents-atom) 1)
        (map #(make-inverted-node cc [% ic]) 
             (hfs-children (adjust-hfs-reward (abstract-hfs-fn) base-reward)))
      (map #(make-upward-node cc parent-pair % base-reward) @results-atom))))

(defn make-inverted-node [cc [hfs parent-ic :as hfs-ic-pair]]
  (is/SimpleNode 
   (conj (hfs-name hfs) parent-ic) (:reward hfs) nil 
   (lazy-seq ((if (seq (:remaining-actions hfs)) add-cache-parent add-cache-result) cc hfs-ic-pair))
   nil))

(defn make-upward-node [cc [hfs ic] child-hfs base-reward]
  (let [lifted (adjust-hfs-reward (lift-hfs hfs child-hfs) (- base-reward))]
    (if ic (make-inverted-node cc [lifted ic]) (hfs->simple-node lifted))))

(defn make-inverted-search [state action]
  (is/make-flat-incremental-dijkstra 
   (make-inverted-node (HashMap.) [(make-root-hfs state action) nil])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; SAHA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here, subsearches should only generate goal nodes. So, we only have to deal with 
; expanding the initial nodes we populate the search with.  These can be dummies. 

;; TODO: these should all be single-solution . Note: sequence enforces this ? 
;; These caches cache erfinements, optimsitic descriptions, and solve final-state connection probelm
; Refinements and valuation for abstracted SA

(declare get-saha-sps-search)

;; TODO: smarter about failed searches... ?
(defn get-inner-sa-cache "Get a map from inner final states to SAS nodes."[hfs]
  (let [[name abstract-hfs-fn] (drop-hfs hfs)]
    (util/cache-with *problem-cache* name
      (let [inner-hfs (abstract-hfs-fn)
            inner-name (hfs-name inner-hfs)
            {:keys [state remaining-actions]} inner-hfs
            next-hfs  (lazy-seq (hfs-children inner-hfs))]
        (into {}
          (for [[ss sr] (env/optimistic-map (util/safe-singleton remaining-actions) state)]
            [ss 
             (is/cache-incremental-search
              (is/make-delayed-search :dummy (is/SimpleSummary sr)
                (delay                      
                 (is/make-recursive-incremental-dijkstra
                  (is/SimpleNode (conj inner-name ss) sr nil
                                 (map hfs->simple-node (remove #(and (empty? (:remaining-actions %))
                                                                     (not (= (:state %) ss)))
                                                               next-hfs)) nil)
                  (fn [n] [(get-saha-sps-search (:data n) ss) 0 identity])))))]))))))

(defn get-outer-sa-cache "Get a map from outer final states to SAS nodes/" [hfs]
  (util/cache-with *problem-cache* (hfs-name hfs)
    (util/map-keys #(lift-state (:state hfs) %) (get-inner-sa-cache hfs))))

(defn get-saha-sas-search [hfs final-state] ((force ((get-outer-sa-cache hfs) final-state))))

;; TODO: remove expensive names.
(defn get-saha-sps-search [hfs final-state]
;  (println "\nget-sps" hfs final-state) (Thread/sleep 100)
  (let [r-a (:remaining-actions hfs)]
    (assert (seq r-a))
    (if (util/singleton? r-a)
        (get-saha-sas-search hfs final-state)
      (is/get-cached-search *problem-cache* (conj (hfs-name hfs) final-state)                    
        (is/make-recursive-incremental-dijkstra 
         (is/SimpleNode (conj (hfs-name hfs) final-state) (:reward hfs) nil
           (for [[ss sas-maker] (get-outer-sa-cache (first-action-hfs hfs))]
             (is/SimpleNode (conj (hfs-name hfs) ss final-state) 0 nil nil [ss ((force sas-maker))])) nil)
         (fn [n]
           (let [[ss sas] (:data n)
                 next-sps (get-saha-sps-search (rest-actions-hfs hfs ss) final-state)]
             [(is/make-closed-sequence-search n (force sas) next-sps (fn [x y] x))
              0 identity])))))))

;(is/make-flat-incremental-dijkstra (hfs->simple-node hfs))


(defn make-saha-search [state action]
  (get-saha-sas-search (make-root-hfs state action) 
                       (util/safe-singleton (keys (env/optimistic-map action state)))))



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
          top  (search-maker init tla)]
      (is/first-solution-reward-pair top))))



(defn sahucs-simple-flat [henv]
  (hierarchical-search henv nil make-simple-flat-search))

;; Equivalent to above but slower.
(defn sahucs-flat [henv]
  (hierarchical-search henv nil make-flat-search))

(defn sahucs-simple [henv]
  (hierarchical-search henv nil make-recursive-search))

(defn sahucs-inverted [henv]
  (hierarchical-search henv nil make-inverted-search))

(defn saha-simple [henv]
  (hierarchical-search henv nil make-saha-search))



