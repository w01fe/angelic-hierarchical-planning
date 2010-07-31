(ns angelic.search.incremental.hierarchical
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]
            [angelic.env.util :as env-util] 
            [angelic.hierarchy :as hierarchy]
            [angelic.search.incremental.core :as is])
  (:import  [java.util HashMap]))


; Angelic hierarchy of optimal incremental searches

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def #^HashMap *problem-cache* nil)
(def *state-abstraction?* true)
(def *full-context* :dummy)  ; used if state abstraction off.


;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchical Forward State ;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord HierarchicalForwardState [state reward opt-sol remaining-actions])
(defn make-hierarchical-forward-state [state reward opt-sol remaining-actions]
  (HierarchicalForwardState. state reward opt-sol remaining-actions))

(defn hfs-name 
  ([hfs] [(:state hfs) (map env/action-name (:remaining-actions hfs))])
  ([hfs more-name] (conj (hfs-name hfs) more-name)))

(defn hfs-pretty-name [hfs]
  [(map env/action-name (:opt-sol hfs))
   :THEN
   (map env/action-name (:remaining-actions hfs))])

(defn hfs-solution-pair [hfs]
  (when hfs
   (assert (empty? (:remaining-actions hfs)))
   [(:opt-sol hfs) (:reward hfs)]))

(defn make-root-hfs [state action]
  (make-hierarchical-forward-state state 0 [] [action]))

(defn hfs-children [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (when-let [[f & r] (seq remaining-actions)]      
      (if (env/primitive? f)
        (when-let [[ss sr] (and (env/applicable? f state) (env/successor f state))]
          [(make-hierarchical-forward-state ss (+ reward sr) (conj opt-sol f) r)]) 
        (for [ref (hierarchy/immediate-refinements f state)]
          (make-hierarchical-forward-state state reward opt-sol (concat ref r)))))))

(defn combine-hfs [n1 n2 state-combiner action-combiner]
  (make-hierarchical-forward-state
   (state-combiner       (:state n1)   (:state n2))
   (+                    (:reward n1)  (:reward n2))
   (into                 (:opt-sol n1) (:opt-sol n2))
   (action-combiner      (:remaining-actions n1) (:remaining-actions n2))))

;; Sub and lift -- used by recursive, inverted, saha (drop only)
(defn hfs-first-sub-name "Name for first abstracted subproblem of hfs" [hfs]
  (let [{[f] :remaining-actions state :state} hfs]
    [(if *state-abstraction?* (state/extract-context state (env/precondition-context f state)) state) 
     (env/action-name f)]))

(defn hfs-first-sub "First abstracted subproblem of hfs" [hfs]
  (let [{[f] :remaining-actions state :state} hfs]
    (make-root-hfs (state/get-logger state (if *state-abstraction?* (env/precondition-context f state) *full-context*)) f)))

(defn lift-hfs "Lift child-solution into the context of parent-node, counterpart to sub."
  [parent child] 
  (combine-hfs parent child state/transfer-effects
               (fn [r1 r2] (util/assert-is (empty? r2)) (next r1))))


;; Used for inverted only
(defn adjust-hfs-reward [h r]
  (make-hierarchical-forward-state (:state h) (+ r (:reward h)) (:opt-sol h) (:remaining-actions h)))

; used for saha only
(defn first-action-hfs "Return hfs for just first action." [hfs]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (make-hierarchical-forward-state state 0 nil (take 1 remaining-actions))))

(defn rest-actions-hfs "Return hfs for just first action." [hfs mid-state]
  (let [{:keys [state reward opt-sol remaining-actions]} hfs]
    (assert (seq remaining-actions)) (assert (zero? reward)) (assert (empty? opt-sol))
    (make-hierarchical-forward-state mid-state 0 nil (drop 1 remaining-actions))))

;; TODO: remove expensive assertino.
(defn join-hfs [parent-hfs first-result rest-result final-state]
  (combine-hfs first-result rest-result (constantly final-state) (constantly nil))
#_  (let [my-final (reduce env/transfer-effects (:state parent-hfs)
                         [(:state first-result) (:state rest-result)])]
    (util/assert-is (= (dissoc (state/as-map final-state) :const) 
                       (dissoc (state/as-map my-final) :const)))
    (combine-hfs first-result rest-result (constantly my-final) (constantly nil))))



(defn hfs-can-reach? [hfs s]
  (or (seq (:remaining-actions hfs)) (= s (:state hfs))))

(defn hfs-cycle-level [hfs]
  (when-let [a (first (:remaining-actions hfs))] (hierarchy/cycle-level a (:state hfs))))

(defn hfs-gg "Return gg-hfs and goal-map, or nil if not gg." [hfs]
  (let [a (util/safe-singleton (:remaining-actions hfs))]
    (when-let [[gga goal-map] (hierarchy/gg-action a)]
      [(make-hierarchical-forward-state (:state hfs) (:reward hfs) (:opt-sol hfs) [gga])
       goal-map
       (every? (env/precondition-context a (:state hfs)) (keys goal-map))])))

(defn hfs-optimistic-map [hfs]
  (let [{:keys [state remaining-actions]} hfs]
#_    (apply println "Optimistic map for " (hfs-first-sub-name hfs) "is\n"
             (for [[s r] (hierarchy/optimistic-map (util/safe-singleton remaining-actions) state)]
               (str "  " (env/extract-effects s) ": " r "\n")))
    (hierarchy/optimistic-map (util/safe-singleton remaining-actions) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HFS & Nodes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn hfs->simple-node 
  ([hfs] (is/make-simple-node (hfs-name hfs) (:reward hfs) (empty? (:remaining-actions hfs)) hfs))
  ([hfs extra-data] (hfs->simple-node hfs extra-data (empty? (:remaining-actions hfs))))
  ([hfs extra-data goal?] ; for inverted, needs non-goal goal-looking nodes.
     (is/make-simple-node (conj (hfs-name hfs) extra-data) (:reward hfs) goal? [hfs extra-data]))
  ([hfs extra-data goal? rew] ; for saha, needs estimated reward.
     (is/make-simple-node (conj (hfs-name hfs) extra-data) rew goal? [hfs extra-data])))


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
  (is/make-wrapped-subsearch
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
        (fn [n] (let [s (:state (:data n))] (map #(state/get-var s %) goal-vars)))
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
(defrecord InvertedCache [results-atom parents-atom base-reward])

(defn add-cache-result [_ [hfs ic :as hfs-ic-pair]]
  (let [{:keys [results-atom parents-atom base-reward]} ic]
    (when-let [o (peek @results-atom)] (util/assert-is (<= (:reward hfs) (:reward o))))
    (swap! results-atom conj hfs)
    (map #(make-upward-node % hfs base-reward) @parents-atom)))

(defn add-cache-parent [#^HashMap cc [parent-hfs parent-ic :as parent-pair]]
  (let [ic (util/cache-with cc (hfs-first-sub-name parent-hfs) 
             (InvertedCache. (atom []) (atom []) (:reward parent-hfs)))
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

;; TODO: version that includes pessimistic costs
;; TODO: version that does smarter search based on optimistic counts.

(declare get-saha-sps-search)


(defn get-sas-map "Get a map from outer final states to SAS nodes/" [hfs]
  (util/cache-with *problem-cache* (hfs-name hfs) ; unabstracted state SA cache
    (util/map-keys #(state/transfer-effects (:state hfs) %)
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

;; Note: may legitimately get to wrong final-state, if some refs reach some states.
;(def *bad-args* nil)
(defn get-saha-sas-search [hfs final-state] 
#_  (let [f ((get-sas-map hfs) final-state)]
    (when-not f (def *bad-args* [hfs final-state])
              (println "Got bad final-state: " (hfs-name hfs) (hfs-first-sub-name hfs)))
    (f))
  (if-let [f ((get-sas-map hfs) final-state)]
    (f)
    (do #_(println "Miss! " (hfs-first-sub-name hfs) final-state) is/failed-search)))


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
                   #_(println (hfs->simple-node hfs) (state/extract-effects final-state)
                            (state/extract-effects (:state (first (:data g1))))
                            (state/extract-effects (:state (first (:data g2))))
                            )
                   (hfs->simple-node (join-hfs hfs (first (:data g1)) (first (:data g2)) final-state) 
                                     :goal)))))))))))


(defn make-saha-search [root-hfs]
  (get-saha-sas-search root-hfs (util/safe-singleton (keys (hfs-optimistic-map root-hfs)))))

;; TODO: version with better meta-level control, PN-style. 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; AHA* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simplified version of AHA* that only works on concrete states, and doesn't
; use pessimistic descriptions (only primitive) for pruning.  
; Loses forward-caching, Adds tail-caching.

; or abstract-lookahead-tree.
; instead, do caching of tails.


(defn compute-heuristic [state remaining-actions]
  (if (empty? remaining-actions) 0
      (util/cache-with *problem-cache* [state remaining-actions]
        (let [[f & r] remaining-actions]
          (apply max is/neg-inf
            (for [[ss sr] (hierarchy/optimistic-map f state)]
              (+ sr (compute-heuristic ss r))))))))


(defn hfs->aha-star-node [hfs]
  (is/make-simple-node 
   (hfs-name hfs) 
   (+ (:reward hfs) (compute-heuristic (:state hfs) (:remaining-actions hfs))) 
   (empty? (:remaining-actions hfs)) 
   hfs))

(defn make-aha-star-simple-search [root-hfs]
  (is/make-flat-incremental-dijkstra 
   (hfs->aha-star-node root-hfs) 
   #(->> % :data hfs-children (map hfs->aha-star-node))))


(comment (defn print-heuristic* [state remaining-actions pad]
   (if (empty? remaining-actions) 0
       (let [[f & r] remaining-actions]
         (apply max is/neg-inf
                (for [[ss sr] (hierarchy/optimistic-map f state)]
                  (do (println pad (select-keys (state/as-map state) [ [:base] [:gripper-offset]]) (env/action-name f) sr)
                      (+ sr (print-heuristic* ss r (str pad "  ")))))))))

         (defn print-heuristic [hfs] (print-heuristic* (:state hfs) (:remaining-actions hfs) "")))
(comment ; replace anon with this to test for heuristic inconsistencies.
  #(let [children (->> % :data hfs-children (map hfs->aha-star-node))]
      (doseq [c children] (util/assert-is (<= (is/max-reward c) (is/max-reward %))
                                          "%s" [ (angelic.discrete-manipulation/state-str (:state (:data %)))
                                                 (map env/action-name (:remaining-actions (:data %)))
                                                 (map env/action-name (:remaining-actions (:data c)))
                                                  (print-heuristic (:data %))
                                                  (println "\n\n")
                                                  (print-heuristic (:data c))
                                                 ]
                                          ))
      children))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Top-level  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn generic-hierarchical-search 
  ([henv sol-hfs-fn] (generic-hierarchical-search henv sol-hfs-fn true))
  ([henv sol-hfs-fn sa?]
     (let [e    (hierarchy/env henv)
           init (env-util/initial-logging-state e)
           tla  (hierarchy/hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
       (binding [*problem-cache*    (HashMap.)
                 *state-abstraction?* sa?
                 *full-context*      (if sa? :dummy (state/current-context init))]
         (sol-hfs-fn (make-root-hfs init tla))))))

(defn simple-hierarchical-search 
  ([hfs search-maker sa?] (simple-hierarchical-search hfs search-maker sa? identity))
  ([hfs search-maker sa? sol-extract-fn]
     (generic-hierarchical-search hfs (comp hfs-solution-pair sol-extract-fn :data is/first-goal-node search-maker) sa?)))

; Decomposed Angelic State-abstracted Hierarchical (Uniform-cost/A*)
(defn h-ucs      [henv] (simple-hierarchical-search henv make-flat-search false))
(defn h-ucs-fast [henv] (simple-hierarchical-search henv make-fast-flat-search false))
(defn dh-ucs     [henv] (simple-hierarchical-search henv make-recursive-search false))
(defn dsh-ucs    [henv] (simple-hierarchical-search henv make-recursive-search true))
(defn dsh-ucs-dijkstra [henv] (simple-hierarchical-search henv make-acyclic-recursive-search true))
(defn dsh-ucs-gg [henv] (simple-hierarchical-search henv make-gg-search true))
(defn dsh-ucs-inverted [henv] (simple-hierarchical-search henv make-inverted-search true))
(defn explicit-simple-dash-a* [henv] (simple-hierarchical-search henv make-saha-search true first))

(defn explicit-simple-ah-a* [henv] (simple-hierarchical-search henv make-aha-star-simple-search false))
(defn explicit-simple-dah-a* [henv] (simple-hierarchical-search henv make-saha-search false first))

(def aaai-algs
     [["H-UCS" h-ucs]
      ["DH-UCS" dh-ucs]
      ["DSH-UCS" dsh-ucs]
;      ["DSHU-d" dshu-dijkstra]
      ["AH-A" explicit-simple-ah-a*]
      ["DAH-A" explicit-simple-dah-a*]
      ["DASH-A" explicit-simple-dash-a*]])

(def aaai-alg-map (into {} aaai-algs))



(defn interactive-hierarchical-search [henv]
  (let [e    (hierarchy/env henv)
        tla  (hierarchy/hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)])]
    (interactive/generic-interactive-search 
     (make-root-hfs (env/initial-state e) tla)
     :reward
     hfs-children
     #(empty? (:remaining-actions %))
     hfs-pretty-name)))

(comment
  (do (use '[angelic env hierarchy taxi ucs hierarchical-incremental-search] 'edu.berkeley.ai.util) (require '[angelic sahucs-simple sahucs-simple-dijkstra sahucs-inverted saha-simple] '[angelic.old ahois]))
   (let [e (make-random-taxi-env 5 5 5 3) _ (println e) h (simple-taxi-hierarchy e)]  
    (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
    (doseq [alg `[sahucs-flat sahucs-fast-flat angelic.sahucs-simple/sahucs-simple sahucs-simple angelic.sahucs-simple-dijkstra/sahucs-simple-dijkstra sahucs-dijkstra angelic.sahucs-inverted/sahucs-inverted sahucs-inverted angelic.saha-simple/saha-simple saha-simple ]]
      (time (println alg (run-counted #(debug 0 (second ((resolve alg) h)))))))))

(comment
 (let [e (angelic.taxi/make-random-taxi-env 5 5 5 3) _ (println e) h (angelic.taxi/simple-taxi-hierarchy e)]  
   (time (println "ucs" (run-counted #(second (uniform-cost-search e)))))
   (doseq [alg `[saha-simple ]]
     (time (println alg (run-counted #(debug 0 (second ((resolve alg) h)))))))))