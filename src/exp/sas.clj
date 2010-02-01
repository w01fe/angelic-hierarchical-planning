(ns exp.sas
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util [queues :as queues] [graphviz :as gv]]
            [exp [env :as env] causal-graphs [hierarchy :as hierarchy]])
  (:import [java.util LinkedList HashMap HashSet ArrayList])
  )


(deftype SAS-Var     [name vals])

;; SAS-Problem will always have a special action [:goal] and var :goal with init [:false], desired [:true]. 
(deftype SAS-Problem [vars init actions actions-fn]
  env/Env
    (initial-state [] init)
    (actions-fn    [] actions-fn)
    (goal-fn       [] #(= (util/safe-get % :goal) [:true]))
  env/FactoredEnv 
    (goal-map      [] {:goal [:true]}))

(defn make-simple-successor-generator [vars actions]
;  (println (count vars) (count actions))
  (cond (empty? vars)    (constantly actions)
        (empty? actions) (constantly nil)
        :else            
          (let [[var & more-vars] vars
                var-name          (:name var)
                actions-by-val    (util/group-by #((:precond-map %) var-name) actions)]
            (if (= (count actions-by-val) 1)
                (if (nil? (key (first actions-by-val)))
                    (make-simple-successor-generator more-vars actions)
                  (let [v  (key (first actions-by-val))
                        sg (make-simple-successor-generator more-vars actions)]
                    (fn successor-gen2 [s] (when (= v (env/get-var s var-name)) (sg s)))))
              (let [dc-sg   (make-simple-successor-generator more-vars (get actions-by-val nil)) 
                    val-sgs (util/map-vals #(make-simple-successor-generator more-vars %) actions-by-val)]
                (fn successor-gen [s] (concat (dc-sg s) (when-let [f (val-sgs (env/get-var s var-name))] (f s)))))))))

(defn make-sas-problem [vars init actions]
  (SAS-Problem vars init actions (make-simple-successor-generator (vals vars) actions)))


(def *working-dir* "/tmp/")
(def *lama-dir* "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/")

(defn lama-translate [stem]
  (util/sh (str *lama-dir* "translate/translate.py") (str stem "-domain.pddl") (str stem ".pddl")
           :dir *working-dir*))


(defn map-ize [key-fn s]
  (into {}
    (loop [s s, result nil]
      (if (empty? s) result
        (let [[k & r] s
              [vs r]  (split-with (complement key-fn) r)]
;          (println vs)
          (assert (key-fn k))
          (recur r (cons [ (key-fn k) vs] result)))))))

(defn read-groups-file
  "Read a groups file from LAMA and output a map from variable names to atoms."
  [file]
  (util/map-vals 
   (fn [vl] (map #(let [tokens (remove empty? (.split #^String % "[,() ]"))]
                    (if (= (second tokens) "Atom")
                        (do (assert (not (= (nth tokens 2) "other")))
                            (vec (map keyword (drop 2 tokens))))
                      [:other])) 
                 vl))
   (map-ize #(when-not (.startsWith #^String % " ") 
               (keyword (.substring #^String % 0 (dec (count %)))))
            (.split #^String (slurp file) "\n"))))

(defn expand-condition [vars [varn valn]]
  (let [var (nth vars varn)]
    [(:name var) (nth (:vals var) valn)]))

(defn make-sas-problem-from-pddl [stem]
  (lama-translate stem)
;  (println (lama-translate stem))
  (let [var-map (assoc (read-groups-file (str *working-dir* "test.groups"))
                  :goal [[:false] [:true]])
        sas-q   (LinkedList. (seq (.split #^String (slurp (str *working-dir* "output.sas")) "\n")))
        _       (dotimes [_ 3] (.pop sas-q))
        _       (assert (= (.pop sas-q) "begin_variables"))
        n-vars  (read-string (.pop sas-q))
        vars-ds (doall (for [_ (range n-vars) 
                             :let [[v ds] (.split #^String (.pop sas-q) " ")]]
                         (do (assert (not (= v "goal")))
                             [(keyword v) (read-string ds)])))
        _       (assert (= (.pop sas-q) "end_variables"))
        vars    (vec (for [[i [n ds]] (util/indexed (concat vars-ds [[:goal 2]]))]
                       (let [var-info (util/safe-get var-map n)]
                         (SAS-Var n (vec var-info)))))
        _       (assert (= (.pop sas-q) "begin_state"))
        init-v  (vec (for [_ (range n-vars)] (read-string (.pop sas-q))))
        _       (assert (= (.pop sas-q) "end_state"))        
        _       (assert (= (.pop sas-q) "begin_goal"))
        goal-m  (into {} (for [_ (range (read-string (.pop sas-q)))]
                           (read-string (str "[" (.pop sas-q) "]"))))
        _       (assert (= (.pop sas-q) "end_goal"))
        ops     (doall (for [_ (range (read-string (.pop sas-q)))]
                         (let [_        (assert (= (.pop sas-q) "begin_operator")) 
                               name     (vec (map keyword (.split #^String (.pop sas-q) " ")))
                               prevails (doall (for [_ (range (read-string (.pop sas-q)))]
                                                 (read-string (str "[" (.pop sas-q) "]"))))
                               effects  (doall (for [_ (range (read-string (.pop sas-q)))]
                                                 (read-string (str "[" (.pop sas-q) "]"))))  
                               cost     (read-string (.pop sas-q))]
                           (assert (not (= (first name) :goal)))
                           (assert (= (.pop sas-q) "end_operator"))
                           (assert (seq effects))
                           (assert (apply distinct? (concat (map first prevails)
                                                            (map #(nth % 1) effects))))
                           (assert (every? #(= 0 (first %)) effects))
                           (env/FactoredPrimitive 
                            name
                            (into {} (map (partial expand-condition vars)
                                          (concat (for [[_ v ov] effects :when (not (= ov -1))] [v ov]) 
                                                  prevails)))
                            (into {} (map (partial expand-condition vars) (for [[_ v _ nv] effects] [v nv])))
                            (if (= cost 0) -1 (- cost))))))]
    (make-sas-problem 
     (into {} (map (juxt :name identity) vars)) 
     (util/map-map (partial expand-condition vars) (util/indexed (conj init-v 0)))
     (conj (vec ops) 
           (env/FactoredPrimitive [:goal] (util/map-map (partial expand-condition vars) goal-m) 
                                  {:goal [:true]} 0)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simplification stuff ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn merge-vals
  ([] nil)
  ([x] x)
  ([x y] (cons ::or (map #(if (= (first %) ::or) (next %) [%]) [x y])))
  ([x y & more] (reduce merge-vals x (cons y more))))

;; Idea is: multiple untested vals per var can be merged, unset vals can be removed.
;;          Then, any var with 1 val can be removed entirely.
(defn simplify-sas-problem [vars actions init untested-vals unset-vals dead-actions]
  (let [unset-vals-v     (util/map-vals #(set (map second %)) (util/group-by first unset-vals))
        untst-vals-v     (util/map-vals #(set (map second %)) (util/group-by first untested-vals))
        val-mappings     (util/map-vals 
                          #(let [unset-vals (or (unset-vals-v (:name %)) {})
                                 untst-vals (clojure.set/difference (or (untst-vals-v (:name %)) {}))
                                 merged-val (apply merge-vals untst-vals)]
                             (merge (util/identity-map (:vals %))
                                    (into {} (map vector unset-vals (repeat nil)))
                                    (into {} (map vector untst-vals (repeat merged-val))))) 
                          vars)
        final-vars       (into {}
                           (for [[vn var] vars
                                 :let [val-map  (val-mappings vn)
                                       new-vals (vec (distinct (vals val-map)))
                                       _ (assert (and (> (count new-vals) 0)
                                                      (val-map (init vn))))]
                                 :when (> (count new-vals) 1)]
                             [vn (SAS-Var vn new-vals)]))
        final-actions    (vec (for [a (remove (set dead-actions) actions)
                                    :let [fp (into {} (for [[var val] (:precond-map a)
                                                            :when (contains? final-vars var)]
                                                        [var (util/make-safe ((val-mappings var) val))]))
                                          fe (into {} (for [[var val] (:effect-map a)
                                                            :let [new-val ((val-mappings var) val)]
                                                            :when (and (contains? final-vars var) new-val)]
                                                        [var new-val]))]
                                    :when (seq fe)]
                                (env/FactoredPrimitive (:name a) fp fe (:reward a))))]
    (println "Removing"   (- (count actions) (count final-actions)) "actions," 
                            (count dead-actions) "initial;" 
                          (- (count vars) (count final-vars)) "vars;"
                          (apply + (for [[vn nv] final-vars] 
                                     (- (count (:vals (vars vn))) (count (:vals nv))))) "additional vals.")
    (make-sas-problem
     final-vars
     (select-keys init (keys final-vars))
     final-actions)))

;; Forward simplification
;; Can merge all values for a var that are never referenced in a precondition,
;; Remove all values that are never set by an effect. 
;; Then, remove actions with invalid preconditions or no effects.
(defn forward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        untested-vals               (HashSet.)
        unset-vals                  (HashSet.)
        action-precond-counts       (HashMap.)
        actions-by-precond          (HashMap.)
        stack                       (queues/make-stack-pq)]
    (doseq [var (vals (dissoc vars :goal)), val (:vals var)] 
      (.add untested-vals [(:name var) val])
      (.add unset-vals [(:name var) val]))
    (doseq [[var val] init] (.remove unset-vals [var val]))
    (doseq [a actions]
      (.put action-precond-counts a (count (:precond-map a)))
      (when (empty? (:precond-map a)) (queues/pq-add! stack a 0))
      (doseq [[var val] (:effect-map a)] (.remove unset-vals [var val]))
      (doseq [[var val] (:precond-map a)]
        (.remove untested-vals [var val])
        (.put actions-by-precond [var val] (cons a (.get actions-by-precond [var val])))))
    (queues/pq-add! stack (env/FactoredPrimitive [:init] {} init 0) 0)
    (while (not (queues/pq-empty? stack))
        (doseq [[var val] (:effect-map (queues/pq-remove-min! stack))
                a (.remove actions-by-precond [var val])]
          (let [c (dec (.remove action-precond-counts a))]
            (if (> c 0)
                (.put action-precond-counts a c)
              (queues/pq-add! stack a 0)))))
;    (println (util/map-vals count (util/group-by first  untested-vals)))
    (println (count unset-vals) (count untested-vals) (count actions-by-precond) (count action-precond-counts))
    (simplify-sas-problem vars actions init untested-vals (concat unset-vals (keys actions-by-precond)) 
                          (keys action-precond-counts))))


;; Do static look at actions and find equivalent vals
 ; These are: ones that are always set at the same time, AND
 ; all ways of unsetting them unset both.  Slow for now.
(defn canonical-vv [pair] (sort-by first pair))

; map from vars to map from vals to [next-val [actions]]
(defn make-extended-dtgs [vars actions]
  (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
          (for [a actions
                [evar eval] (:effect-map a)
                pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                :when       (not (= eval pval))]
            [[evar pval eval] a])))

; map from vars to map from vals to [prev-val [actions]]
(defn make-extended-reverse-dtgs [vars actions]
  (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
          (for [a actions
                [evar eval] (:effect-map a)
                pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                :when       (not (= eval pval))]
            [[evar eval pval] a])))

(defn find-static-equivalence-pairs [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        actions                     (cons (env/FactoredPrimitive [:init] {} init 0) actions)
        extended-dtgs               (make-extended-dtgs vars actions)
        extended-rdtgs              (make-extended-reverse-dtgs vars actions)]
    (filter
     (fn [[[var1 val1] [var2 val2]]]
       (when (< (.compareTo #^Comparable var1 #^Comparable var2) 0)
         (every? (fn [[var val other-var other-val]]
                   (every? (fn [a] (not (= (get (:effect-map a) other-var other-val) other-val)))
                           (apply concat (vals ((extended-dtgs var) val)))))
                 [[var1 val1 var2 val2] [var2 val2 var1 val1]])))
     (apply concat
            (for [[vn extended-rdtg] extended-rdtgs
                  [val incoming-map] extended-rdtg]
              (disj (apply clojure.set/intersection (map #(set (map (juxt (constantly [vn val]) vec) (:effect-map %))) 
                                                         (apply concat (vals incoming-map)))) 
                    [vn val]))))))

(defn find-static-equivalence-sets [sas-problem]
  (let [pairs           (find-static-equivalence-pairs sas-problem)
        symmetric-pairs (apply concat (for [[x y] pairs] [[x y] [y x]]))]
    (loop [remaining-map (util/map-vals #(set (map second %)) (util/group-by first symmetric-pairs)), results nil]
      (if (empty? remaining-map) results
        (let [[fk fs] (first remaining-map)]
          (let [all 
                (loop [cur (conj fs fk)]
                  (let [nxt (apply clojure.set/union (map (partial get remaining-map) cur))]
                    (if (= cur nxt) cur (recur nxt))))]
            (recur (apply dissoc remaining-map all) (cons all results))))))))

;;Return a mapping from vars to val-remappings
; In some weird cases, right set of vars to eliminate may be non-obvious.
;;In more cases, right val to choose may be non-obvious.
;; Algorithm: find redundant vars (easy), pick deletes 
;; TODO: if two vars have same domain size, and n-1 proven equivs, are equiv.
(defn find-redundant-vars 
  ([sas-problem] (find-redundant-vars sas-problem (find-static-equivalence-sets sas-problem)))
  ([sas-problem equiv-sets]
     (let [vars           (:vars sas-problem)
           redundant-vars (set (map first (filter (fn [[x xxx]] (let [vc (count (:vals (vars x))) rc (count xxx)]
                                                                  (assert (<= rc vc)) 
                                                                  (or (= vc rc) )))
                                                  (util/group-by first (apply concat equiv-sets)))))
           val-equivs     (reduce (fn [m [ks v]] (assoc-in m ks v))
                                  {}
                                  (for [equiv-set equiv-sets, [var val :as p] equiv-set
                                        :when (contains? redundant-vars var)]
                                    [[var val] (disj equiv-set p)]))
           var-equivs     (util/map-vals 
                           (fn [equiv-map] (apply clojure.set/intersection (map #(set (map first %)) (vals equiv-map))))
                           val-equivs)
           equiv-graph    (for [[k vs] var-equivs, v vs] [k v])
           [scc-graph scc-nodes] (exp.causal-graphs/scc-graph equiv-graph)]
       (assert (every? (partial apply =) scc-graph))
       (println (count redundant-vars) "redundant vars in" (count scc-nodes) "equivalence classes;"
                "can remove" (- (count redundant-vars) (count scc-nodes))) 
       (map set (vals scc-nodes)))))

(defn equivalence-info [sas-problem]
  (let [equiv-sets     (find-static-equivalence-sets sas-problem)
        var-equiv-sets (find-redundant-vars sas-problem equiv-sets)
        all-equiv-vars (apply clojure.set/union var-equiv-sets)
        rem-equiv-sets (remove empty?
                        (for [es equiv-sets]
                          (if (some all-equiv-vars (map first es))
                            (let [rem (set (remove #(all-equiv-vars (first %)) es))]
                              (when (seq rem) (conj rem [:es :???])))
                            es)))]
    (println "Remaining equivalences: " (count rem-equiv-sets))
    rem-equiv-sets))

(defn sas-sample-files [n]
  (into {}
    (concat  
      [["2x2-taxi"  (exp.taxi/write-taxi-strips (exp.taxi/make-random-taxi-env 2 2 2 1))]]
      (for [domain ["elevators" "openstacks" "parcprinter" "pegsol" "scanalyzer" #_ "sokoban" "transport" "woodworking"]]
        [(str "IPC6-" domain)
         (str "/Users/jawolfe/Projects/research/IPC/ipc2008-no-cybersec/seq-opt/" domain "-strips/p"
              (if (< n 10) (str "0" n) (str n)))]))
    
        )
  )

; (doseq [ [n f] (sas-sample-files 1)] (println "\n\n"  n) (equivalence-info (make-sas-problem-from-pddl f)))


 ; make implicit persist actions.  
;; Run planning graph, with mutexes
 ; state layer is pair [allowed-vv-set allowed-vv-pair-set]
 ; action layer is [allowed-actions mutex-actions]
;; Can do similar queue-based scheme:
 ; New action available can add to vv-set, allowed-vv-pair-set in obvious way.
  ; (note implicit mutex with implicit persist actions for vxv in preconds,
  ;  all vars in effects)
 ; New val available can add actions, 

;; State to action layer:
; actions are permanent mutex if 

(comment 
  (defn canonical-vv [pair] (sort-by first pair))
  (defn canonical-aa [pair] (sort-by :name pair))

  (defn next-action-layer [[new-vals new-val-pairs] ....]
    ;; Find new actions - indexed by # of preconds + precond pairs left to go.
  
    ;; Find new action pairs - can be 
                                        ; (1) 
  
    (.addAll live-vals new-vals)
    (.addAll live-val-pairs new-val-pairs)
    )

;; Do simple forward analysis, and return [equiv-vals mutex-vals]
  (defn find-mutexes [sas-problem]
    (let [{:keys [vars actions init]} sas-problem
          vars                        (apply sorted-map (apply concat vars))
          persist-actions             (for [[vn var] vars, val (:vals var)] (SAS-Action [:persist vn val] {vn val} {vn val} 0))
          live-vals                   (HashSet.)
          live-val-pairs              (HashSet.)
          live-actions                (HashSet.)
          live-action-pairs           (HashSet.)]

      ;; Fill in initial live-action-pairs ? 
      (loop [[new-vals new-val-pairs] [(map vec init)  (distinct (map vec (for [v1 init, v2 init] (canonical-vv [v1 v2]))))]]
        (if (empty? new-val-pairs) [(count live-vals) (count live-val-pairs) (count live-actions) (count live-action-pairs)]
            (recur (next-state-layer
                    (next-action-layer
                     [new-vals new-val-pairs]
                     ...
                     )
                    ...)))))))

;;;;;;;;;;;;;;;;;;;;;;;;


;; Backward simplification: 
;; Can remove anything provably not on a shortest path to goal.  
;; Basically, this comes down to finding irrelevant "spokes" in DTGs and removing them. 
;; Should also provide things like: never pick up a passenger you've already put down ?
;; Ideally, at the top-level would prune everything based on actual shortest paths...

;; SO, do pruning as we walk up.  Do need to precompute causal graph?
;; Idea: Collect all actions below.  Project onto ancestors of current node.
;; Can sometimes use goal to know final value, project upwards.  May or may not help.
;; Collect all actions on acyclic paths from (init+projected(w/o goal)) to (projected)

;; How do we handle cycles?  Must go around until nothing changes?

;; How do we compute actions on acyclic paths?  
;; Exists an acyclic path ...

;; Be careful; action with multiple effects must add other effects to sources lists.

(defn make-map-of-sets [keys]
  (let [h (HashMap.)]
    (doseq [key keys] (.put h key (HashSet.)))
    h))

(defn add-mos [#^HashMap mos key val]
  (.add #^HashSet (.get mos key) val))

(defn add-mos-new [#^HashSet dirty #^HashMap oldmos #^HashMap newmos key val]
  (when-not (.contains #^HashSet (.get oldmos key) val)
    (.add dirty key)
    (.add #^HashSet (.get newmos key) val)))

(defn edge-list->map [el]
  (persistent! (reduce (fn [m [k v]] (assoc m k (cons v (m k)))) (transient {}) el)))



(defn exhaustive-dfs [src dst extended-dtg stack-set #^HashSet new-action-pool #^HashSet new-actions]
  (cond (= src dst)               true
        (contains? stack-set src) false
        :else 
          (let [new-stack-set (conj stack-set src)]            
            (some (fn [[nval actions]]
                    (when (exhaustive-dfs nval dst extended-dtg new-stack-set new-action-pool new-actions)
                      (doseq [a actions :when (.contains new-action-pool a)] (.add new-actions a))
                      true))
                  (get extended-dtg src)))))

;; For now, terribly inefficient. 
;; Treating goals specially sould definitaly help.
(defn backward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        extended-dtgs               (make-extended-dtgs vars actions)     
        dead-actions                (HashSet. #^java.util.Collection actions)
        now-live-actions            (HashSet.)
        new-goals                   (make-map-of-sets (keys vars))
        new-srcs                    (make-map-of-sets (keys vars))
        old-goals                   (make-map-of-sets (keys vars))
        old-srcs                    (make-map-of-sets (keys vars))
        dirty-var-set               (HashSet.)]
    (doseq [[var val] init] (add-mos old-srcs var val))
    (add-mos new-goals :goal [:true])
    (.add dirty-var-set :goal)
    (println (count dead-actions))
    
    (while (not (.isEmpty dirty-var-set))
      (let [var (first dirty-var-set)]
        (println "doing" var)
        (while (or (not (.isEmpty #^HashSet (get new-goals var))) (not (.isEmpty #^HashSet (get new-srcs var))))
          (if (not (empty? (get new-goals var)))
            (let [new-goal (first (get new-goals var))]
              (println " doing goal" new-goal)
              (doseq [old-src (get old-srcs var)]
                (assert (exhaustive-dfs old-src new-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove #^HashSet (get new-goals var) new-goal)
              (.add    #^HashSet (get old-goals var) new-goal))
            (let [new-src (first (get new-srcs var))]
              (println " doing src" new-src)              
              (doseq [old-goal (get old-goals var)]
                (assert (exhaustive-dfs new-src old-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove #^HashSet (get new-srcs var) new-src)
              (.add    #^HashSet (get old-srcs var) new-src)))
          (doseq [a (seq now-live-actions)]
            (doseq [[pvar pval] (:precond-map a)]
              (add-mos-new dirty-var-set old-goals new-goals pvar pval))
            (doseq [[evar eval] (:effect-map a)]
              (add-mos-new dirty-var-set old-srcs new-srcs evar eval)))
          (.removeAll dead-actions now-live-actions)
          (.clear now-live-actions))
        (.remove dirty-var-set var)))
    
    (println dead-actions)))

 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy induction! ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *vars* nil)
(def *reverse-dtgs* nil)
(def #^HashMap *hla-cache* (HashMap.)) ; a map from [action-name] to map from init-sets to action.

(defprotocol SAS-Induced-Action
  (precond-var-set [a])
  (initial-sets    [a])
  (effect-sets     [a]))

(extend ::env/FactoredPrimitive
  SAS-Induced-Action
    {:precond-var-set (fn [a] (util/keyset (:precond-map a)))
     :initial-sets    (fn [a] (util/map-vals (fn [x] #{x}) (:precond-map a)))
     :effect-sets     (fn [a] (util/map-vals (fn [x] #{x}) (:effect-map a)))})

(defn vv-hla-name [var val] [::VV var val])
(deftype SAS-VV-HLA     [var val precond-vars init-sets effect-sets refinements]
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (initial-sets    [] init-sets)
    (effect-sets     [] effect-sets)
  env/Action
    (action-name [] (vv-hla-name var val))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (assert (util/subset? (util/keyset effect-sets) precond-vars)) precond-vars)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] refinements)
    (cycle-level-           [s] nil))

(defn action-hla-name [action] [::A (env/action-name action)])
(deftype SAS-Action-HLA [action  precond-vars init-sets effect-sets refinements]
  SAS-Induced-Action
    (precond-var-set [] precond-vars)
    (initial-sets    [] init-sets)
    (effect-sets     [] effect-sets)
  env/Action
    (action-name [] (action-hla-name action))
    (primitive?  [] false)
  env/ContextualAction 
    (precondition-context [s] (assert (util/subset? (util/keyset effect-sets) precond-vars)) precond-vars)
  hierarchy/HighLevelAction
    (immediate-refinements- [s] refinements)
    (cycle-level-           [s] nil))

(defn find-all-acyclic-paths 
  ([var init-val-set goal-val reverse-dtg]
     (find-all-acyclic-paths var init-val-set goal-val reverse-dtg nil #{} true))
  ([var init-val-set goal-val reverse-dtg plan-suffix stack-val-set can-use-free?]
;     (println "FACP" var init-val-set goal-val)
     (when (and (seq init-val-set) (not (contains? stack-val-set goal-val)))
       (if (contains? init-val-set goal-val)
           (cons plan-suffix 
                 (find-all-acyclic-paths var (disj init-val-set goal-val) goal-val reverse-dtg plan-suffix 
                                         stack-val-set can-use-free?))
         (apply concat
           (for [[pval actions] (get reverse-dtg goal-val)
                 a              actions
                 :let  [action-free? (not (contains? (:precond-map a) var))]
                 :when (or (not action-free?) can-use-free?)]
             (find-all-acyclic-paths var init-val-set pval reverse-dtg (cons a plan-suffix) 
                                     (conj stack-val-set goal-val) (and can-use-free? (not action-free?)))))))))

(declare induce-action-hla)

;    (println paths)
;    (doseq [path paths] (induce-action-hla (first path) init-sets ))

(defn progress-refinement [prim-ref init-sets ]
  (println "Progressing plan" prim-ref)
  (loop [prim-ref prim-ref, hla-ref [], plan-effect-sets {}]
    (if (empty? prim-ref)
        [hla-ref plan-effect-sets]
      (let [a     (first prim-ref)
            hla-a (induce-action-hla a (merge init-sets plan-effect-sets) )]
        (recur (rest prim-ref) (conj hla-ref hla-a) (merge plan-effect-sets (effect-sets hla-a)))))))

;; Want to look at acyclic paths, which include at most one free-action. (with no precond on var.)
;; Two things we can do here; recursive style (works from any src, more caching) or direct style
 ;; (avoid cycles, more focused description/pruning, but less caching and less general). 

(defn induce-vv-hla- [var goal-val init-sets]
  (println "Inducing HLA to get" var "to val" goal-val "from" (init-sets var))
  (let [inits        (init-sets var)
        reverse-dtg  (*reverse-dtgs* var)
        paths        (find-all-acyclic-paths var inits goal-val reverse-dtg)
        refs-results (filter identity (map #(progress-refinement % init-sets ) paths))]
    (if (and (util/singleton? refs-results) (util/singleton? (ffirst refs-results)))
        (first (ffirst refs-results))
      (when (seq refs-results)
        (assert (apply = (map util/keyset (map second refs-results)))) ;; Otherwise, no-effect not handled properly when not in PC.
        (SAS-VV-HLA var goal-val 
                    (set (for [[ref _] refs-results, a ref, v (precond-var-set a)] v))
                    init-sets 
                    (apply merge-with clojure.set/union (map second refs-results))
                    (map first refs-results))))))


(defn induce-action-hla- [a init-sets ]
  (println "Inducing HLA for preconds + action" (:name a))
  (let [first-bits (for [[pvar pval] (:precond-map a)
                         :when (not (= (init-sets pvar) #{pval}))]
                     (induce-vv-hla pvar pval init-sets ))]
    (doall first-bits)
;    (println (:name a) (count first-bits))
;    (doseq [b first-bits] (println "\n" (env/action-name b) "\n\n"))
    (when (every? identity first-bits)
     (if (empty? first-bits)
         a
       (let [bit (util/safe-singleton first-bits)]
         (assert (= ((effect-sets bit) (:var bit)) #{(:val bit)}))
         (SAS-Action-HLA 
          a 
          (clojure.set/union (util/keyset (:precond-map a)) (precond-var-set bit))
          init-sets
          (merge (effect-sets bit) (util/map-vals (fn [x] #{x}) (:effect-map a)))
          [[bit a]]))))))


;; TODO: figure out how much to generalize here.
(defn cached-induce [name init-sets result-fn]
  (let [entries (.get *hla-cache* name)]
    (assert (not (identical? entries :STACK)))
    (if-let [v (first (filter #(let [ks (precond-var-set %)] 
                                 (= (select-keys init-sets ks) (select-keys (initial-sets %) ks))) 
                              entries))]
        (do (println "Cache hit for" name) 
            v)
      (do (.put *hla-cache* name :STACK)
          (let [ret (result-fn)]
            (assert ret) ;; If we run into this, need to figure out how to properly cache failures.
            (.put *hla-cache* name (cons ret entries))
            ret)))))

(defn induce-action-hla [a init-sets]
  (cached-induce (action-hla-name a) init-sets #(induce-action-hla- a init-sets)))

(defn induce-vv-hla [var goal-val init-sets ]
  (cached-induce (vv-hla-name var goal-val) init-sets #(induce-vv-hla- var goal-val init-sets)))

(defn induce-hierarchy [sas-problem]
  (let [{:keys [vars actions init]} sas-problem]
    (binding [*vars*         vars
              *reverse-dtgs* (make-extended-reverse-dtgs vars actions)
              *hla-cache*    (HashMap.)              
              ]
      (hierarchy/SimpleHierarchicalEnv sas-problem 
        [(util/make-safe 
          (induce-action-hla (util/safe-singleton (get-in *reverse-dtgs* [:goal [:true] [:false]]))
                             (util/map-vals (fn [x] #{x}) init)))]))))





(defmulti pretty-print-action type)

(defn pretty-print-hla [h]
  (println (str "\nRefs for HLA" (env/action-name h)) (precond-var-set h) #_ (effect-sets h))
  (doseq [ref (:refinements h)]
    (println " " (util/str-join ", " (map env/action-name ref))))
  (doseq [ref (:refinements h), a ref]
    (pretty-print-action a)))

(defmethod pretty-print-action ::SAS-VV-HLA [h] (pretty-print-hla h))
(defmethod pretty-print-action ::SAS-Action-HLA [h] (pretty-print-hla h))
(defmethod pretty-print-action ::env/FactoredPrimitive [h] nil)


(defn pretty-print-hierarchy [hierarchy]
  (pretty-print-action (first (:initial-plan hierarchy))))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Causal graph stuff ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn compute-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (for [action actions
           precondition (concat (:precond-map action) (:effect-map action))
           effect       (:effect-map action)]
       [(first precondition) (first effect)]))))

(defn compute-relaxed-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (concat (for [vn (keys vars)] [vn vn])
             (for [action actions
                   precondition (:precond-map action)
                   effect       (:effect-map action)]
               [(first precondition) (first effect)])))))


;; This is analogous to delete-list relaxation...
(defn compute-relaxed-full-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (apply concat 
           (for [a actions]
             (concat (for [[var val] (:precond-map a)] [[var val] (:name a)])
                     (for [[var val] (:effect-map  a)] [(:name a) [var val]]))))))

(defn compute-dtgs [sas-problem]
  (let [{:keys [vars actions]} sas-problem
        outer                  (HashMap.)]
    (doseq [var (keys vars)] (.put outer var (HashSet.)))
    (doseq [a actions
            [evar eval] (:effect-map a)
            pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
            :when       (not (= eval pval))]
      (.add #^HashSet (.get outer evar) [pval eval]))
    (util/map-vals set (into {} outer))))

(defn show-dtgs [sas-problem]
  (gv/graphviz-el
   (for [[vn edges] (compute-dtgs sas-problem)
         [s d] edges]
     [(cons vn s) (cons vn d)])))

(defn show-master-graph [sas-problem]
  (let [cg   (compute-causal-graph sas-problem)
        dtgs (compute-dtgs sas-problem)]
    (gv/graphviz-el
     (remove #(apply = %)
             (apply concat cg 
                    (for [[vn var] (:vars sas-problem)
                          val      (:vals var)]
                      [vn val])
                    (vals dtgs))))))

