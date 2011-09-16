(ns angelic.scripts.thesis
 (:require [angelic.util :as util]  
	   [angelic.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.search.textbook :as textbook]
           [angelic.domains.discrete-manipulation :as dm]
           [angelic.domains.dash :as dd]           
           [angelic.domains.nav-switch :as ns]
           [angelic.search.explicit.hierarchical :as hes]
           [angelic.search.implicit
            [ah-astar :as aha]
            [sahtn :as sahtn]
            [dash-astar-opt :as dao]
            [dash-astar-opt-simple :as daos]
            [dash-astar :as da]
            [dash-astar-old :as oda]
            ]
           [angelic.search.explicit.depth-first :as dfbb]
           ))


;;;;;;;;;;;;;;;;;; Helpers  ;;;;;;;;;;;;;;;;;;;;;;;;;

(defn median-of [n items]
  (assert (odd? n))
  (let [ind (quot n 2)]
    (when (> (count items) ind)    
      (nth (sort items) ind))))

(defn solution-lengths [ds k nper]
  (util/map-vals (fn [es] (median-of nper (map #(count (first (:output %))) es)))
                 (group-by k
                  (filter #(and (= (:alg %) :dash-a*) (:ms %)) ds))))

(defn pad-right [x n]  
  (let [xs (str x) 
        s ^String (str "                               " xs)]
    (assert (<= (.length xs) n))
    (.substring s (- (.length s) n))))

(defn format-n [n dec]
  (let [base (util/expt 10 dec)]
    (/ (int (* base n)) (if (> dec 0) (double base) 1))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *exp-result* ::ExpResult)

(defstruct exp-result 
  :class :experiment :commit-id :timeout? :memout? :output :printed :init-ms :ms :mb
  :next-count :opt-count :pess-count :ref-count :plan-count)

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
  (env/reset-next-counter)
  (hierarchy/reset-ref-counter))

(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (struct exp-result ::ExpResult
          experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
          (util/sref-get env/*next-counter*)
          (util/sref-get hierarchy/*optimistic-counter*)
          (util/sref-get hierarchy/*pessimistic-counter*)
          (util/sref-get hierarchy/*ref-counter*)
          (util/sref-get hierarchy/*plan-counter*)))

(defmacro defresults [name es-maker]
  (let [sn (util/symbol-cat '* name '-results*)]
    `(do (defonce ~sn nil)
         (defn ~(util/symbol-cat 'read- name '-results) []
           (def ~sn
                (experiments/experiment-set-results->dataset
                 (experiments/read-experiment-set-results (~es-maker))))))))

(def alg-forms
     {:sahtn   (fn [m] `(sahtn/sahtn ~'init #{:nav :reach :discretem-tla '~'top '~'navh '~'navv}))
      :aha*    (fn [m] `(aha/ah-a* ~'init true))
      :dash-a* (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                                  :choice-fn rand-nth))})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Nav Switch experiments ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO! with split-nav, pruning fail.

(defn run-timed [f]
  (try
    (let [[r t] (util/get-time-pair (hierarchy/run-counted f))] (conj r t))
    (catch Exception e (println e))))

(defn ns-test []
  (let [s (rand-int 100)
        e (ns/make-random-nav-switch-env 20 3 s)
        h (ns/make-nav-switch-hierarchy e false #_ true);; TODO: split?
        o (second (textbook/uniform-cost-search e true))]
    (println "seed" s "\n")
    (doseq [[n a]
            [["dijkstra "#(textbook/uniform-cost-search e true)]
             ["a*" #(textbook/a*-search e ns/simple-ns-heuristic true)]

             #_ ["dfbb" #(dfbb/dfbb h)]
             #_["opt-dfbb" #(dfbb/dfbb h o)]
             #_ ["graph-dfbb" #(dfbb/graph-dfbb h)]
             #_ ["graph-opt-dfbb" #(dfbb/graph-dfbb h o)]

             #_["sahtn" #(sahtn/sahtn h #{:nav :reach :discretem-tla
                                        'top 'nav 'navh 'navv})]

             ["h-ucs" #(hes/h-ucs-fast h)]
             ["dsh-ucs" #(hes/dsh-ucs h)]
             ["dij-dsh-ucs" #(hes/dsh-ucs-dijkstra h)]
             ["inv-dsh-ucs" #(hes/dsh-ucs-inverted h)]

             ["optimistic-ah-a*" #(aha/optimistic-ah-a* h true)]
             ["strict-ah-a*" #(aha/strict-ah-a* h true)]
             ["full-ah-a*" #(aha/full-ah-a* h true)]                          

             ["explicit-ah-a*" #(hes/explicit-simple-ah-a* h)]
             ["explicit-dash-a*" #(hes/explicit-simple-dash-a* h)]

             ["ao-l-dash-a*" #(da/implicit-dash-a* h)]
             ["ao-f-dash-a*" #(da/implicit-dash-a* h :choice-fn first)]
             ["ldfs-l-dash-a*" #(da/implicit-dash-a* h :search-strategy :ldfs)]
             ["ao-l-dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical)]
             ["ao-f-dash-a*" #(da/implicit-dash-a* h :choice-fn first :collect? :hierarchical)]
             ["ldfs-l-dash-a*" #(da/implicit-dash-a* h :search-strategy :ldfs :collect? :hierarchical)]              
             ]]
      (println (pad-right n 20)
               (update-in (run-timed a) [0 0] count)))))

(defn shallowest [level-map]
  (fn [s]
    (apply
     min-key
     #(util/safe-get level-map (-> % :name second angelic.search.function-sets/fs-name first))
     s)))

(defn dm-test [& args]
  (let [e (apply dm/make-random-hard-discrete-manipulation-env args)
        h (dm/make-discrete-manipulation-hierarchy e)
        o (second (da/implicit-dash-a* h))]
    (doseq [[n f]
            [#_ ["dijkstra "#(textbook/uniform-cost-search e true)]
             #_ ["a*" #(textbook/a*-search e ns/simple-ns-heuristic true)]

             #_ ["dfbb" #(dfbb/dfbb h)]
             #_ ["opt-dfbb" #(dfbb/dfbb h o)]
             #_ ["graph-dfbb" #(dfbb/graph-dfbb h)]
             #_ ["graph-opt-dfbb" #(dfbb/graph-dfbb h o)]

             #_ ["sahtn" #(sahtn/sahtn h #{:nav :reach :discretem-tla
                                        'top 'nav 'navh 'navv})]

             #_ ["h-ucs" #(hes/h-ucs-fast h)]
             #_ ["dsh-ucs" #(hes/dsh-ucs h)]
             #_ ["dij-dsh-ucs" #(hes/dsh-ucs-dijkstra h)]
             #_ ["inv-dsh-ucs" #(hes/dsh-ucs-inverted h)]

         #_    ["optimistic-ah-a*" #(aha/optimistic-ah-a* h false)]
         #_    ["strict-ah-a*" #(aha/strict-ah-a* h false)]
         #_    ["full-ah-a*" #(aha/full-ah-a* h false)]
         #_    ["optimistic-ah-a*" #(aha/optimistic-ah-a* h true)]
             ["strict-ah-a*" #(aha/strict-ah-a* h true)]
             ["full-ah-a*" #(aha/full-ah-a* h true)]                                       

             ["explicit-ah-a*" #(hes/explicit-simple-ah-a* h)]
             ["explicit-dash-a*" #(hes/explicit-simple-dash-a* h)]

             ["nps-dash-a*" #(da/implicit-dash-a* h :propagate-subsumption? false)]
             ["ldfs-dash-a*" #(da/implicit-dash-a* h :search-strategy :ldfs)]
             ["dash-a*" #(da/implicit-dash-a* h)]
             ["first-dash-a*" #(da/implicit-dash-a* h :choice-fn first)]             
             ["shallowest-dash-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global
                          :choice-fn (shallowest {:discretem-tla 0
                                                  :move-to-goal 1
                                                  :go-grasp 2 :go-drop 2
                                                  :go-drop-at 3
                                                  :grasp 4 :drop-at 4
                                                  :move-base 5
                                                  :nav 6
                                                  :reach 7
                                                  }))]
             ["h-first-dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical)]
             ["h-shallowest-dash-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global :collect? :hierarchical
                          :choice-fn (shallowest {:discretem-tla 0
                                                  :move-to-goal 1
                                                  :go-grasp 2 :go-drop 2
                                                  :go-drop-at 3
                                                  :grasp 4 :drop-at 4
                                                  :move-base 5
                                                  :nav 6
                                                  :reach 7
                                                  }))]
             
             ]]
      (println (pad-right n 20)
               (update-in (run-timed f) [0 0] count)))))

(defn interpolating-heuristic [w depth]
  #(+ w (* (- 1.0 w) (/ % depth))))

(defn top? [r]
  (when-let [n (-> r :ts-sp :name)]
    (when (= (first n) :Pair)
      (let [n (nth n 2)]
        (when (= (first n) :SA)
          (let [n (angelic.search.function-sets/fs-name (second (second n)))]
;            (println (= n [:dash-tla])) (Thread/sleep 100)
            (= n [:dash-tla])))))))

(defn flast-choice [s]
  (if (top? (last s))
    (last s)
    (first s)))

;; TODO: first-last ordering.
;; Note: right factoring is crucial! (hsould also sub-factor tla refs?)
;; hierarchical hurts here.
(defn dd-test [sps depth target]
  (let [e (dd/make-dash-env sps depth target)
        h8i (dd/make-dash-hierarchy e (interpolating-heuristic 0.9 depth))
        o (* (:nsp e) (:nv e))]
    (println o)
    (doseq [[n f]
            [#_ ["dijkstra "#(textbook/uniform-cost-search e true)]
             ["dash-a*" #(da/implicit-dash-a* h8i)]
             #_ ["1.0-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 1) true)]
             ["0.9-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 0.9) true)]
             #_ ["0.8-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 0.8) true)]
             
             #_ ["1.0-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 1))  true)]
             #_ ["0.9-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 0.9)) true)]
             #_ ["0.8-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 0.8))  true)]
             ["0.8i-opt-ah-a*" #(aha/optimistic-ah-a* h8i true)]

             ["inv-dsh-ucs" #(hes/dsh-ucs-inverted h8i)]
             
             ["dash-a*" #(da/implicit-dash-a* h8i)]
             #_ ["explicit-ah-a*" #(hes/explicit-simple-ah-a* h1)]
             ]]
      (println (pad-right n 20)
               (update-in (run-timed f) [0 0] count)))))

(defn dash-test []
  (doseq [[an h]
          (take 100
           [["nav" (ns/make-nav-switch-hierarchy (ns/make-random-nav-switch-env 20 5 0) false)]
            ["dm1" (dm/make-discrete-manipulation-hierarchy (dm/make-random-hard-discrete-manipulation-env 2 1))]
            ["dm2" (dm/make-discrete-manipulation-hierarchy (dm/make-random-discrete-manipulation-env 3 1))]
            ["dm3" (dm/make-discrete-manipulation-hierarchy (dm/make-random-discrete-manipulation-env 4 6))]
            ["dm3" (dm/make-discrete-manipulation-hierarchy (dm/make-random-discrete-manipulation-env 4 2))]
            ["dm3" (dm/make-discrete-manipulation-hierarchy (dm/make-random-discrete-manipulation-env 4 1))]
            ["dm3" (dm/make-discrete-manipulation-hierarchy (dm/make-random-discrete-manipulation-env 4 7))]
            ])
          [n f]
          [["dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical)]
           ["dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical :search-strategy :ldfs
                                            :choice-fn rand-nth)]
           #_["dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical :choice-fn first)]
           #_["dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical :choice-fn rand-nth)]
           #_ ["old dash-a*" #(oda/implicit-dash-a* h)]]]
    (println an (pad-right n 20) (update-in (run-timed f) [0 0] count))))

;; note: sahtn with dijkstra, not as described.
;; note: right now dfbb set to shuffle.
;; note: explicit algs effectively use different, more accurate heuristics.

;; TODO: queue counts.




(def +ns-sizes+ [5 10 20 50 100 200 500])

(defn make-ns-exp-set []
  (experiments/make-experiment-set "11thesis-ns"
    [:product
     [:size   +ns-sizes+]
     [:alg    (keys alg-forms)]
     [:rand   [0 1 2]]]
    (fn [m]
      `(ns/make-nav-switch-hierarchy
        (ns/make-random-nav-switch-env ~(:size m) 20 ~(:rand m)) true))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.thesis nil #_ 10 3600 512 false ::ExpResult))

(defn make-ns-dd-exp-set []
  (experiments/make-experiment-set "11thesis-ns-dd"
    [:product
     [:size   +ns-sizes+]
     [:alg    [:dash-a*-dijkstra]]
     [:rand   [0 1 2]]]
    (fn [m]
      `(ns/make-nav-switch-hierarchy
        (ns/make-random-nav-switch-env ~(:size m) 20 ~(:rand m)) true))
    (fn [m] `(dao/implicit-dash-a*-opt ~'init :gather true :d true :s :eager :dir :right
                                       :choice-fn rand-nth :dijkstra #{'~'navv '~'navh}))
    'angelic.scripts.thesis nil #_ 10 3600 512 false ::ExpResult))

(defresults ns make-ns-exp-set)
(defresults ns-dd make-ns-dd-exp-set)


;; DASH-A* blows the stack on the cluster for no good reason, so I'm running
;; those experiments locally.

#_ (let [es (make-ns-exp-set)]
     (doseq [[i e] (indexed es)]
      (when (= (:alg (:parameters e)) :dash-a*)
        (run-experiment-set! es i (inc i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Discrete manipulation experiments ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-dm-exp-set []
  (experiments/make-experiment-set "11thesis-dm"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:alg     (keys alg-forms)]
     [:rand    [0 1 2 3 4]]]
    (fn [m]
      `(dm/make-discrete-manipulation-hierarchy
        (dm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m))))
    (fn [m] ((util/safe-get alg-forms (:alg m)) m))
    'angelic.scripts.thesis 10 3600 1024 false ::ExpResult))

(defn make-dm-lama-exp-set []
  (experiments/make-experiment-set "11thesis-dm-lama"
    [:product
     [:objects [1 2 3 4 5 6]]
     [:rand    [1 2 3]]
     [:alg     [:lama]]]
    (fn [m]
      `(dm/make-random-hard-discrete-manipulation-env ~(:objects m) ~(:rand m)))
    (fn [m] `(dm/solve-dmh-lama ~'init))
    'angelic.scripts.thesis nil 3600 512 false ::ExpResult))


(defresults dm make-dm-exp-set)
(defresults dm-lama make-dm-lama-exp-set)


(defn read-all-results [] (read-dm-results) (read-dm-lama-results))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Discrete charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;






;(use '[angelic.util experiments cluster] 'angelic.scripts.thesis)
;(run-experiment-set-cluster (make-dm-exp-set))

;; (time (run-experiment-set! (make-dm-lama-exp-set) 6 9))

;; (plot (ds->chart (experiment-set-results->dataset res) [:alg] :objects :ms {:key "top left" } {} first))

