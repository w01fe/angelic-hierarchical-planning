(ns angelic.search.implicit.ah-astar
  (:require [edu.berkeley.ai.util :as util]
            [angelic.search.function-sets :as fs]
            [angelic.search.explicit.core :as is])
  (:import  [java.util HashMap]))


;; Simple implicit version of AHA* with implicit descriptions,
;; and limited pruning.

;; Keep graph queue of (input set, tail plan),
;; where tail starts at first HLA.

;; Optional pruning of strictly dominated optimistic tails.


 ; bind to HashMap from name to solved-reward-to-state.
(def ^HashMap *pruning-cache* nil)


(defrecord Plan [input-set input-reward opt-sol fs-seq output-set output-reward])

(defn plan-name [plan]
  [(:input-set plan) (map fs/fs-name (:fs-seq plan))])

(defn make-plan [pre-sol input-set input-reward remaining-fs]
  (loop [init-set input-set init-reward input-reward
         input-set input-set input-reward input-reward
         remaining-fs remaining-fs final-fs [] sol pre-sol]
    (if (empty? remaining-fs)
      (Plan. init-set init-reward sol final-fs input-set input-reward)
      (let [[fs & more-fs] remaining-fs
            [out-set step-rew stat :as outcome] (fs/apply-opt fs input-set)
            out-rew (+ input-reward step-rew)]
        (when out-set
         (when (= stat :blocked) (util/assert-is (not (empty? final-fs)) "%s" [fs #_ (def *bad* [fs input-set])]))
         (if (and (empty? final-fs) (= stat :solved))
           (do #_ (util/assert-is (empty? final-fs) "%s" [fs])
               (when-let [^HashMap pc *pruning-cache*]
                 (let [k [out-set (map fs/fs-name more-fs)]]
                   (.put *pruning-cache* k (max out-rew (get *pruning-cache* k Double/NEGATIVE_INFINITY)))))
               (recur out-set out-rew out-set out-rew more-fs [] (conj sol fs)))
           (when (or (not *pruning-cache*)
                     (let [^HashMap pc *pruning-cache*
                           k [out-set (map fs/fs-name more-fs)]
                           r (.get pc k)]
                       (or (not r) (> out-rew r))))
             (recur init-set init-reward out-set out-rew more-fs (conj final-fs fs) sol))))))))

(defn plan-refinements [p]
  (keep
   #(make-plan (:opt-sol p) (:input-set p) (:input-reward p) (concat % (next (:fs-seq p))))
   (fs/child-seqs (first (:fs-seq p)) (:input-set p))))


(defn plan->implicit-aha-star-node [plan]
;  (println (:input-reward plan) (:output-reward plan) (second (plan-name plan)))
  (is/make-simple-node (plan-name plan) (:output-reward plan) (empty? (:fs-seq plan)) plan))

(defn make-aha-star-simple-search [root-plan]
  (is/make-flat-incremental-dijkstra 
   (plan->implicit-aha-star-node root-plan)
   #(->> % :data plan-refinements (map plan->implicit-aha-star-node))))

(defn ah-a* [henv pruning?]
  (binding [*pruning-cache*  (when pruning? (HashMap.))]
    (let [[init-ss root-fs] (fs/make-init-pair henv)]    
      (when-let [g (-> (make-plan [] init-ss 0 [root-fs])
                       make-aha-star-simple-search
                       is/first-goal-node
                       :data)]
        [(remove #(= (first %) :noop) (map fs/fs-name (:opt-sol g)))
         (:output-reward g)]))))

;; (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 1 3))]   (time (println (run-counted #(identity (ah-a* h false)))))))
;; (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 1 3))]   (time (println (run-counted #(identity (ah-a* h false)))))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h  (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 1 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*))  (time (println (run-counted #(identity (ah-a* h true))))))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 4 0) true)]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*))  (time (println (run-counted #(identity (ah-a* h true))))))))

;; TODO: ImplicitAHA*Env




(comment ;; For debugging, I guess?

  ;            [angelic.env :as env]
;            [angelic.hierarchy :as hierarchy]
;            [angelic.hierarchy.util :as hierarchy-util]            
;            [angelic.hierarchy.state-set :as state-set]
;            [angelic.hierarchy.angelic :as angelic]

(defrecord ImplicitAHA*FEnv [henv]
  env/Env
  (initial-state [_]
    (let [e    (hierarchy/env henv)
          init (env-util/initial-logging-state e)
          tla  (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)] 0)]
      (-> (make-action-node [(state-set/make-logging-factored-state-set [init]) 0 true] {} tla)
                       vector
                       make-plan)))
  (actions-fn [_]
    (fn [shp]
      (for [ref (plan-refinements shp)]
        (reify 
         env/Action
         (action-name [_] (plan-name ref))
         env/PrimitiveAction
         (applicable? [_ s] (assert (identical? s shp)) true)
         (next-state-and-reward [_ s]
           (let [old-rew (second (:output-tuple shp))
                 new-rew (second (:output-tuple ref))]
                                        ;             (println old-rew shp new-rew)
             #_(util/assert-is (<= new-rew old-rew) "%s" (print-str shp ref))
             [ref (- new-rew old-rew)]))))))
  (goal-fn [_] (fn [s] (nth (util/safe-get s :output-tuple) 2))))

(defn make-implicit-first-ah-a*-env [henv] (ImplicitAHA*FEnv. henv)))