(ns angelic.sas.simplification
  (:require [angelic.util :as util]
            [angelic [env :as env] [sas :as sas]]
            [angelic.env.util :as env-util]
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
    (sas/make-sas-problem vars init (concat nice-actions fixed-actions))))





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
