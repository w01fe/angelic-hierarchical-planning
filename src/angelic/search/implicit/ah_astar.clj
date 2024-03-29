(ns angelic.search.implicit.ah-astar
  (:use clojure.contrib.core)
  (:require [angelic.util :as util]
            [angelic.util.queues :as queues]
            [angelic.search.function-sets :as fs]
            [angelic.search.explicit.core :as is])
  (:import  [java.util HashMap]))


;; Implicit AHA*, with several pruning options.

;; All algorithms do pruning when a plan is popped.

;; TODO: tiebreaking?

;; opt-sol is a prefix of primitive function sets
;; opt-seq and pess-seq are lazy seqs of tuples representing the rest of plan.
;; tuples are [[reachable-set remaining-fs] reward status]
(defrecord Plan [tupler opt-sol opt-seq pess-seq])

(defmethod print-method angelic.search.implicit.ah-astar.Plan [o s]
  (print-method (str "#<Plan " (first (:opt-seq o)) ">") s))

(defn memo-tuple-seq []
  (let [h (HashMap.)]
    (fn ts* [[[s rfs] r :as init-tuple] next-f]
      (if-let [p (.get h [s rfs next-f])]
        (let [o (- r (second (first p)))]
          (cons init-tuple
           (map
           #(update-in % [1] + o)
           (next p))))
        (let [ret 
              (when s
                (cons
                 init-tuple
                 (lazy-seq
                  (when-let [[fs & rfs] (seq rfs)]
                    (let [[next-s step-r stat] (next-f fs s)]
                      (ts* [[next-s rfs] (+ step-r r) stat] next-f))))))]
          (.put h [s rfs next-f] ret)
          ret)))))

(defn tuple-seq [[[s rfs] r :as init-tuple] next-f]
  (lazy-seq
   (when s
     (cons
      init-tuple
      (when-let [[fs & rfs] (seq rfs)]
        (let [[next-s step-r stat] (next-f fs s)]
          (tuple-seq [[next-s rfs] (+ step-r r) stat] next-f)))))))

(defn split-exact-prefix [opt-seq]
  (let [[e o] (split-with #(= (nth % 2) :solved) opt-seq)]
    [(butlast e) (cons (last e) o)]))

(defn make-plan [tupler opt-sol init-exact]
  (assert (= (nth init-exact 2) :solved))
  (let [[exact-seq opt-seq] (split-exact-prefix (tupler init-exact fs/apply-opt))]
    (if (-> opt-seq last first second empty?)
      (Plan.
       tupler
       (concat opt-sol (for [[[_ [fs]]] exact-seq] fs))
       opt-seq
       (tupler (first opt-seq) fs/apply-pess))
      (util/print-debug 2 "dead-end at " opt-seq )
      )))

(defn plan-refinements [{:keys [tupler opt-sol opt-seq]}]
  (let [[[s rfs] r stat] (first opt-seq)]
;    (println (-> opt-seq last second))
    (assert (= stat :solved))
    (assert (seq rfs))
    (keep
     #(make-plan tupler opt-sol [[s (concat % (next rfs))] r :solved])
     (fs/child-seqs (first rfs) s))))

(defn plan->solution-pair [plan]
  [(->> plan :opt-sol (map fs/fs-name) (remove #(= (first %) :noop)))
   (->  plan :opt-seq util/safe-singleton second)])

(defn henv->root-plan [henv tupler]
  (let [[init-ss root-fs] (fs/make-init-pair henv)]
    (make-plan tupler [] [[init-ss [root-fs]] 0 :solved])))




(defn plan->simple-node [plan]
  (is/make-simple-node 
   (-> plan :opt-seq first)
   (-> plan :opt-seq last second)
   (-> plan :opt-seq first first second empty?)
   plan))

(defn optimistic-ah-a*
  "AHA* with no pessimistic descriptions, but repeated hstate elimination"
  [henv cache-tails?]
  (-?>
   henv (henv->root-plan (if cache-tails? (memo-tuple-seq) tuple-seq)) plan->simple-node
   (is/make-flat-incremental-dijkstra
    #(->> % :data plan-refinements (map plan->simple-node)))
   is/first-goal-node :data plan->solution-pair))

(defn optimistic-ah-a-part*
  "For debugging."
  [ss fs]
  (-?>
   (make-plan (memo-tuple-seq) [] [[ss [fs]] 0 :solved]) plan->simple-node
   (is/make-flat-incremental-dijkstra
    #(->> % :data plan-refinements (map plan->simple-node)))
   is/first-goal-node :data plan->solution-pair))




(defn register-strict! [^HashMap h {:keys [pess-seq]}]
  (doseq [[k r] pess-seq]
    (.put h k (max r (get h k Double/NEGATIVE_INFINITY)))))

(defn strictly-prunable? [^HashMap h {:keys [opt-seq]}]
  (some (fn [[k r]]
          (< r (get h k Double/NEGATIVE_INFINITY))) 
        opt-seq))

(defn strict-ah-a*
  "AHA* with strict pruning and repeated hstate elimination"
  [henv cache-tails?]  
  (let [h (HashMap.)]
    (-?>
     henv (henv->root-plan (if cache-tails? (memo-tuple-seq) tuple-seq)) plan->simple-node
     (is/make-flat-incremental-dijkstra
      (fn [{p :data}]
        (when-not (strictly-prunable? h p)
          (map #(do (register-strict! h %) (plan->simple-node %))
               (plan-refinements p)))))
     is/first-goal-node :data plan->solution-pair)))



(defn plan->tree-node [plan]
  (is/make-simple-node 
   (gensym)
   (-> plan :opt-seq last second)
   (-> plan :opt-seq first first second empty?)
   plan))

(defn register-weak! [^HashMap h name {:keys [pess-seq]}]
;  (println "R" name (-> pess-seq first first second))
  (doseq [[k r] pess-seq]
;    (println name k r)
    (let [[pr nds] (or (get h k) [Double/NEGATIVE_INFINITY #{}])]
      (cond (> r pr) (.put h k [r #{name}])
            (= r pr) (.put h k [r (conj nds name)])))))

(defn deregister-weak! [^HashMap h name {:keys [pess-seq]}]
;  (println "D" name (-> pess-seq first first second))
  (doseq [[k r] pess-seq]
    (when-let [[pr nds] (get h k)]
      (.put h k [pr (disj nds name)]))))

(defn prunable? [^HashMap h {:keys [opt-seq]}]
  (some (fn [[k r]]
          (when-let [[pr nds] (.get h k)]
            (or (when (< r pr) #_ (println "strict") true)
;                (when (and (= r pr) (empty? nds)) (println "almost!" nds))
                (when (and (= r pr) (seq nds)) #_ (println "weak") true)))) 
        opt-seq))

(defn full-ah-a*
  "AHA* with string pruning, weak pruning on live plans, and no other
   repeated hstate elimination."
  [henv cache-tails?]
  (let [h (HashMap.)]
    (-?>
     henv (henv->root-plan (if cache-tails? (memo-tuple-seq) tuple-seq)) plan->tree-node
     (is/make-flat-incremental-dijkstra
      (fn [{p :data n :name}]
        (deregister-weak! h n p)
        (when-not (prunable? h p)
;          (println (-> p :opt-seq first first))
          (map #(let [{:keys [name] :as nd} (plan->tree-node %)]
                  (register-weak! h name %)
                  nd)
               (plan-refinements p)))))
     is/first-goal-node :data plan->solution-pair)))



;; (hierarchy/run-counted #(angelic.search.implicit.ah-astar/optimistic-ah-a* (ns/make-nav-switch-hierarchy (ns/make-random-nav-switch-env 5 2 1) true)))


