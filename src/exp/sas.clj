(ns exp.sas
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util [queues :as queues] [graphviz :as gv]]
            [exp [env :as env]])
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
   (fn [vl] (map #(vec (map keyword (drop 2 (remove empty? (.split #^String % "[,() ]"))))) vl))
   (map-ize #(when-not (.startsWith #^String % " ") 
               (keyword (.substring #^String % 0 (dec (count %)))))
            (.split #^String (slurp file) "\n"))))

(defn expand-condition [vars [varn valn]]
  (let [var (nth vars varn)]
    [(:name var) (nth (:vals var) valn)]))

(defn make-sas-problem-from-pddl [stem]
;  (lama-translate stem)
  (println (lama-translate stem))
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

; map from vars to map from vals to [next-val [actions]]
(defn make-extended-dtgs [vars actions]
  (reduce (fn [m [ks a]] (update-in m ks (partial cons a))) {} 
          (for [a actions
                [evar eval] (:effect-map a)
                pval        (if-let [x ((:precond-map a) evar)] [x] (:vals (vars evar)))
                :when       (not (= eval pval))]
            [[evar pval eval] a])))

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
        dead-actions                (HashSet. actions)
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
        (while (or (not (.isEmpty (get new-goals var))) (not (.isEmpty (get new-srcs var))))
          (if (not (empty? (get new-goals var)))
            (let [new-goal (first (get new-goals var))]
              (println " doing goal" new-goal)
              (doseq [old-src (get old-srcs var)]
                (assert (exhaustive-dfs old-src new-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove (get new-goals var) new-goal)
              (.add    (get old-goals var) new-goal))
            (let [new-src (first (get new-srcs var))]
              (println " doing src" new-src)              
              (doseq [old-goal (get old-goals var)]
                (assert (exhaustive-dfs new-src old-goal (get extended-dtgs var) #{} dead-actions now-live-actions)))
              (.remove (get new-srcs var) new-src)
              (.add    (get old-srcs var) new-src)))
          (doseq [a (seq now-live-actions)]
            (doseq [[pvar pval] (:precond-map a)]
              (add-mos-new dirty-var-set old-goals new-goals pvar pval))
            (doseq [[evar eval] (:effect-map a)]
              (add-mos-new dirty-var-set old-srcs new-srcs evar eval)))
          (.removeAll dead-actions now-live-actions)
          (.clear now-live-actions))
        (.remove dirty-var-set var)))
    
    (println dead-actions)))

 









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

