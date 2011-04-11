(ns angelic.sas.simplification
  (:require [angelic.util :as util]
            [angelic [env :as env] [sas :as sas]]
            [angelic.env.util :as env-util]
            [angelic.util.graphs :as graphs]            
            [angelic.sas.analysis :as sas-analysis]))







;;;;;;;;;;;;;;;;;;;;;;; Eliminating dangling effects

;; Dangling effects are pesky effects without preconditions.
;; Typically the precondition is actually known, the domain designer was just too
;; lazy to write it down.  We can imply them and fill them in.

(defn nice-action? [{:keys [precond-map effect-map]}]
  (every? (partial contains? precond-map) (keys effect-map)))

(defn find-values [mutex-map val-sets v precond-map]
  (let [candidates (apply util/difference (get val-sets v)
                          (for [kv precond-map]
                            (util/keyset (get-in mutex-map [kv v]))))]
    (when-not (= (count candidates) 1)
      (util/print-debug 1 "Got" (count candidates) "candidates" candidates "in" v "for" precond-map))
    candidates))


(defn split-action [mutex-map val-sets a]
  (let [{:keys [precond-map effect-map]} a
        pesky-vars (remove (util/keyset precond-map) (keys effect-map))
        _   (util/do-debug 2 (print "Filling in" a "vars" pesky-vars "with " ))
        missing-vals (for [v pesky-vars] (find-values mutex-map val-sets v precond-map))]
    (util/print-debug 2 missing-vals)
    (for [vls (apply util/cartesian-product missing-vals)]
      (update-in a [:precond-map] into (map vector pesky-vars vls)))))


(defn eliminate-dangling-effects [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        [bad-vals mutex-map dead-actions] (sas-analysis/find-mutexes sas-problem)
        live-actions (remove (set dead-actions) actions)
        [nice-actions pesky-actions] (util/separate nice-action? live-actions)
        val-sets      (util/for-map [{:keys [name vals]} (vals vars)] name (set vals))
        fixed-actions (doall (mapcat #(split-action mutex-map val-sets %) pesky-actions))]
;    (assert (empty? bad-vals))
    (println #_ util/print-debug 1 "Removing" (count dead-actions) "actions, keeping" (count nice-actions)
                       "splitting " (count pesky-actions) "into" (count fixed-actions)
                         ", skipping" (count bad-vals) "bad values, maybe ignoring value combinations.")
    (assoc (sas/make-sas-problem vars init (concat nice-actions fixed-actions)) :mutex-map mutex-map)))



(defn split-merge-action [a new-vv-entries]
  (if (empty? new-vv-entries)
    [a]
    (apply concat
     (for [a (split-merge-action a (next new-vv-entries))]
       (let [{:keys [precond-map effect-map]} a
             [vs vls] (first new-vv-entries)]
         (if (some #(contains? precond-map %) vs)
           (let [pre-subs (set (select-keys precond-map vs))
                 rest-pre (apply dissoc precond-map vs)
                 eff-sub  (select-keys effect-map vs)
                 rest-eff (apply dissoc effect-map vs)
                 pvals    (filter #(util/subset? pre-subs %) vls)
                 ]
             (if (and (= (first (:name a)) :goal) (> (count pvals) 1))
               (cons (assoc a :precond-map (assoc rest-pre vs ::goal))
                     (for [st pvals]
                       (env-util/make-factored-primitive
                        [:tog st] 
                        {vs st}
                        {vs ::goal}
                        0)))               
               (for [st pvals]
                 (assoc a
                   :precond-map (assoc rest-pre vs st)
                   :effect-map (assoc rest-eff vs (set (concat eff-sub (remove (comp (util/keyset eff-sub) first) st))))))))    
           [a]))))))


(defn merge-variables [sas-problem var-sets]
  (let [{:keys [vars actions init]} sas-problem
        mutex-map (:mutex-map sas-problem)
        full-vv-map (util/for-map [v (vals vars)] (:name v) (:vals v))
        old-var-map (apply dissoc vars (apply concat var-sets))
        new-vv-map  (util/for-map [vs var-sets] vs (sas-analysis/allowed-combinations (select-keys full-vv-map vs) mutex-map))
        new-acts (mapcat #(split-merge-action % new-vv-map) actions)]
    (println (util/map-vals count new-vv-map))
    (println "Split " (count actions) "into" (count new-acts))
    (assoc (sas/make-sas-problem
            (into old-var-map
                  (for [[n vs] new-vv-map]
                    [n (sas/make-sas-var n vs)]))
            (reduce (fn [m vs]
                      (assoc (apply dissoc m vs)
                        vs (set (for [v vs] [v (get init v)]))))                    
                    init var-sets)
            new-acts)
      :mutex-map mutex-map)))


(defn fix-printer [sas-problem]
  (let [vars (keys (:vars sas-problem))
        bad (filter #(when-not (keyword? (second %)) (#{:available :uninitialized} (first (second %)))) vars)]
    (merge-variables sas-problem [(set bad)])))

(defn merge-effect-clusters [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        mutex-map (:mutex-map sas-problem)
        prevail-cg (sas-analysis/prevail-causal-graph sas-problem)
        clusters   (filter #(> (count %) 1) (map second (second (graphs/scc-graph prevail-cg))))]
    (println clusters)
    (merge-variables sas-problem clusters)))



;; (debug 3 (do (eliminate-dangling-effects  (second  (nth (sas-sample-problems 0) 0))) nil))

;;;;;;;;;;;;;;;;;;;;;;;;; First attempt at simplifying, not sure if itworks

(defn merge-vals
  ([] nil)
  ([x] x)
  ([x y] (cons ::or (map #(if (= (first %) ::or) (next %) [%]) [x y])))
  ([x y & more] (reduce merge-vals x (cons y more))))


(defn simplify-sas-problem [vars actions init untested-vals unset-vals dead-actions]
  (let [unset-vals-v     (util/map-vals #(set (map second %)) (group-by first unset-vals))
        untst-vals-v     (util/map-vals #(set (map second %)) (group-by first untested-vals))
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
                                                      (val-map (init vn))))
                                       _ (when (<= (count new-vals) 1) (println vn new-vals) )
                                       ]
                                 :when (> (count new-vals) 1)]
                             [vn (angelic.sas.SAS-Var. vn new-vals)]))
        final-actions    (vec (for [a (remove (set dead-actions) actions)
                                    :let [fp (into {} (for [[var val] (:precond-map a)
                                                            :when (contains? final-vars var)]
                                                        [var (util/make-safe ((val-mappings var) val))]))
                                          fe (into {} (for [[var val] (:effect-map a)
                                                            :let [new-val ((val-mappings var) val)]
                                                            :when (and (contains? final-vars var) new-val)]
                                                        [var new-val]))]
                                    :when (seq fe)]
                                (env-util/make-factored-primitive (:name a) fp fe (:reward a))))]
    (println val-mappings)
    (println "Removing"   (- (count actions) (count final-actions)) "actions," 
                            (count dead-actions) "initial;" 
                          (- (count vars) (count final-vars)) "vars;"
                          (apply + (for [[vn nv] final-vars] 
                                     (- (count (:vals (vars vn))) (count (:vals nv))))) "additional vals.")
    (sas/make-sas-problem
     final-vars
     (select-keys init (keys final-vars))
     final-actions)))




(defn forward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem]
    (apply simplify-sas-problem
           vars actions init 
           (sas-analysis/forward-analyze sas-problem))))
