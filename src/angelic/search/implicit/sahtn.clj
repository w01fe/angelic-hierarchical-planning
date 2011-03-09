(ns angelic.search.implicit.sahtn
  (:require [angelic.util :as util]
            [angelic.util.queues :as queues]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap]))


;; SAHTN is a state-abstracted, resolution-optimal HTN planning algorithm.
;; It computes the optimal outcomes of each HLA in each context exactly once,
;; then pieces the results together to produce an optimal solution.

;Implements dijkstra, only correct without mutual recursion...

(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: must not screw with Logging metadata.
(defn- merge-valuations [& vs]
  "Like merge-with max, but preserves metadata of the best key."
  (reduce 
   (fn [v1 v2] 
     (reduce 
      (fn [v1 [k v]]
	(if (<= v (get v1 k Double/NEGATIVE_INFINITY))
	    v1
	  (assoc (dissoc v1 k) k v)))
      v1 v2))
   (or (first vs) {}) (rest vs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           Computing result valuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare sahtn-result)

(def ^HashMap *result-cache* nil)
(def *dijkstra-set* nil)

(defn- sahtn-compute-result-seq [fs-seq v]
  "Compute result valuation for sequence as from valuation v."
  (if (empty? fs-seq) v
    (recur (rest fs-seq)
      (apply merge-valuations
        (for [[ss r] v]
	  (util/map-vals #(+ % r)
  	    (sahtn-result (first fs-seq) ss)))))))  

(defn- sahtn-dijkstra-result [fs ss]
  (let [q (queues/make-graph-search-pq)
        output (HashMap.)]
;    (println "dij" (fs/fs-name fs))
    (queues/pq-add! q [ss [fs]] 0)
    (while (not (queues/pq-empty? q))
      (let [[[cur-ss fs-seq] c] (queues/pq-remove-min-with-cost! q)]
        (if (empty? fs-seq)
          (.put output cur-ss (- c))
          (let [[first-fs & more-fs] fs-seq]
            (if (= (first (fs/fs-name fs)) (first (fs/fs-name first-fs)))
              (doseq [child-seq (fs/child-seqs first-fs cur-ss)]
                (queues/pq-add! q [cur-ss (concat child-seq more-fs)] c))
              (doseq [[out-ss out-rew] (sahtn-result first-fs cur-ss)]
                (queues/pq-add! q [out-ss more-fs] (- c out-rew))))))))
    (into {} output)))


(defn- sahtn-compute-result [fs ss]
  "Compute result valuation for action a from state s."
  (cond (fs/primitive? fs)
        (let [[out-set rew] (fs/apply-opt fs ss)]
          (if out-set {(vary-meta out-set assoc :sol [fs]) rew} {}))

        (*dijkstra-set* (first (fs/fs-name fs)))
        (sahtn-dijkstra-result fs ss)
        
        :else
        (apply merge-valuations
               (for [fs-seq (fs/child-seqs fs ss)]
                 (sahtn-compute-result-seq fs-seq {ss 0})))))

(defn- sahtn-result [fs ss]
  "Memoized result valuation for doing a from s."
  (let [sol             (:sol (meta ss))
        #^HashMap cache *result-cache*
	cache-key       [(fs/fs-name fs) (fs/extract-context fs ss)]
	cache-val       (.get cache cache-key)]
    (util/assert-is (not (= cache-val :in-progress)) "%s" [(fs/fs-name fs)])
    (util/map-keys
     (fn [out-set] (with-meta (fs/transfer-effects ss out-set)
                     {:sol (concat sol (:sol (meta out-set)))}))
     (or cache-val
         (do (.put cache cache-key :in-progress)
             (let [result        (sahtn-compute-result fs (fs/get-logger fs ss))]	
               (.put cache cache-key result)
               result ))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                              Top-level driver
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top-level action, refines to initial set of plans.

;; dijkstra set is set of action prefixes for dijkstra mode.
(defn sahtn [henv dijkstra-set]
  (binding [*result-cache* (HashMap.)
            *dijkstra-set* dijkstra-set]
    (let [[init-ss root-fs]  (fs/make-init-pair henv)
          final-val          (sahtn-result root-fs init-ss)
          [final-ss final-r] (last (sort-by val final-val))]
      (when final-r [(remove #(= (first %) :noop) (map fs/fs-name (:sol (meta final-ss)))) final-r]))))    

(set! *warn-on-reflection* false)


;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 4 2 0) true)]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*))  (time (println (run-counted #(identity (ah-a* h true)))))  (time (println (run-counted #(identity (sahtn h #{'top 'navh 'navv}))))))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-discrete-manipulation-env 1 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*))  #_ (time (println (run-counted #(identity (ah-a* h true)))))  (time (println (run-counted #(identity (sahtn h #{:nav :reach :discretem-tla}))))))))



;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-manipulation-pair nh (get-demo1-world-gazebo 2))]   (time (println (run-counted #(second (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*))  (time (println (run-counted #(second (ah-a* h true)))))  (time (println (run-counted #(second (sahtn h #{:nav :reach :discretem-tla}))))))))