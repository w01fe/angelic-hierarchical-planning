(ns angelic.scripts.thesis
 (:require [angelic.util :as util]  
	   [angelic.util [charts :as charts] [datasets :as datasets] [experiments :as experiments]]
           [angelic [env :as env] [hierarchy :as hierarchy] [sas :as sas]]
           [angelic.search.textbook :as textbook]
           [angelic.domains.discrete-manipulation :as dm]
           [angelic.domains.dash :as dd]           
           [angelic.domains.nav-switch :as ns]
           [angelic.search.summary-graphs-newer :as sgn]
           [angelic.search.explicit.core :as hcore]           
           [angelic.search.explicit.hierarchical :as hes]
           [angelic.search.implicit
            [ah-astar :as aha]
            [sahtn :as sahtn]
;            [dash-astar-opt :as dao]
;            [dash-astar-opt-simple :as daos]
            [dash-astar :as da]
;            [dash-astar-old :as oda]
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
  :next-count :opt-count :pess-count :ref-count :plan-count :eh-queue-count :dash-summary-count :dash-expand-count)

(defmethod experiments/setup-experiment-result ::ExpResult [experiment]
  (env/reset-next-counter)
  (hcore/reset-counters!)
  (hierarchy/reset-ref-counter))

(defmethod experiments/make-experiment-result ::ExpResult 
  [experiment setup-info timeout? memout? output printed init-ms ms mb]
  (struct exp-result ::ExpResult
          experiment (util/git-commit-id) timeout? memout? output printed init-ms ms mb
          (util/sref-get env/*next-counter*)
          (util/sref-get hierarchy/*optimistic-counter*)
          (util/sref-get hierarchy/*pessimistic-counter*)
          (util/sref-get hierarchy/*ref-counter*)
          (util/sref-get hierarchy/*plan-counter*)
          @hcore/*queue-counter*
          @sgn/*summary-counter*
          @da/*expand-counter*
          ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; Nav Switch experiments ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(comment
 (def +ns-sizes+ [5 10 20 50 100 200 500])
 (def +ns-reps+ 3))


(def +ns-sizes+ [5 10 15 20 30 40 50 75 100 150 200 250 300 350 400 450 500])
(def +ns-reps+ 5)

(defn nsh [e] (ns/make-nav-switch-hierarchy e false))
;asdf
(def ns-algs
  [["dijkstra" `(textbook/uniform-cost-search ~'init true)]
   ["astar" `(textbook/a*-search ~'init ns/simple-ns-heuristic true)]

;   ["dfbb" #(dfbb/dfbb h)]
;   ["opt-dfbb" #(dfbb/dfbb h o)]
;   ["graph-dfbb" #(dfbb/graph-dfbb h)]
   ["go-dfbb" `(dfbb/graph-dfbb (nsh ~'init) (* -6 (dec (:width ~'init))))]

   ["sahtn" `(sahtn/sahtn (nsh ~'init) #{:nav :reach :discretem-tla '~'top '~'nav '~'navh '~'navv})]

   ["h-ucs" `(hes/h-ucs-fast (nsh ~'init))]
   ["dsh-ucs" `(hes/dsh-ucs (nsh ~'init))]
;   ["dij-dsh-ucs" `(hes/dsh-ucs-dijkstra (nsh ~'init))]
   ["inv-dsh-ucs" `(hes/dsh-ucs-inverted (nsh ~'init))]

   ["optimistic-ah-astar" `(aha/optimistic-ah-a* (nsh ~'init) true)]
   ["strict-ah-astar" `(aha/strict-ah-a* (nsh ~'init) true)]
   ["full-ah-astar" `(aha/full-ah-a* (nsh ~'init) true)]                          

   ["explicit-ah-astar" `(hes/explicit-simple-ah-a* (nsh ~'init))]
   ["explicit-dash-astar" `(hes/explicit-simple-dash-a* (nsh ~'init))]

   ["dash-astar" `(da/implicit-dash-a* (nsh ~'init))]
   ["dash-astar-first" `(da/implicit-dash-a* (nsh ~'init) :choice-fn first)]
   ["dash-astar-ldfs" `(da/implicit-dash-a* (nsh ~'init) :search-strategy :ldfs)]
   ["dash-astar-hoc" `(da/implicit-dash-a* (nsh ~'init) :collect? :hierarchical)]
   ["dash-astar-nos" `(da/implicit-dash-a* (nsh ~'init) :abstract? false)]
   ["dash-astar-nods" `(da/implicit-dash-a* (nsh ~'init) :abstract? false :decompose? false)]])

(defn make-ns-exps [& [test]]
  (for [[n f] ns-algs]
    [n [(fn [sz rep] 
          (let [size (nth +ns-sizes+ sz)]
            (experiments/make-experiment
             (str n "-" sz "-" rep)
             {:alg n :size-i sz :size size :rep rep}
             'angelic.scripts.thesis
             `(ns/make-random-nav-switch-env ~size 20 ~rep)
             f
             10 3600 512 nil ::ExpResult)))
        (count +ns-sizes+) +ns-reps+]]))

#_ (do (use 'angelic.scripts.thesis 'angelic.util.experiments 'angelic.util.cluster)
       (cluster-smart-runner (make-ns-exps) false (str *default-run-dir* "/thesis-ns2/")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; Discrete Manipulation experiments ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def +dm-sizes+ [1 2 3 4 5 6 7 8 9 10
                 ])
(def +dm-reps+ 5)


(defn shallowest [level-map]
  (fn [s]
    (apply
     min-key
     #(util/safe-get level-map (-> % :name second angelic.search.function-sets/fs-name first))
     s)))

(def shallowest-dm
  (shallowest {:discretem-tla 0
               :move-to-goal 1
               :go-grasp 2 :go-drop 2
               :go-drop-at 3
               :grasp 4 :drop-at 4
               :move-base 5
               :nav 6
               :reach 7}))

(defn dmh [e] (dm/make-discrete-manipulation-hierarchy e))

(def dm-algs
  [["dijkstra" `(textbook/uniform-cost-search ~'init true)]
   #_ ["astar" `(textbook/a*-search ~'init ??? true)]

   ["sahtn" `(sahtn/sahtn (dmh ~'init) #{:nav :reach :discretem-tla '~'top '~'nav '~'navh '~'navv})]

   ["h-ucs" `(hes/h-ucs-fast (dmh ~'init))]
   ["dsh-ucs" `(hes/dsh-ucs (dmh ~'init))]
   ["inv-dsh-ucs" `(hes/dsh-ucs-inverted (dmh ~'init))]

   ["optimistic-ah-astar" `(aha/optimistic-ah-a* (dmh ~'init) true)]
   ["strict-ah-astar" `(aha/strict-ah-a* (dmh ~'init) true)]
   ["full-ah-astar" `(aha/full-ah-a* (dmh ~'init) true)]                          

   ["explicit-ah-astar" `(hes/explicit-simple-ah-a* (dmh ~'init))]
   ["explicit-dash-astar" `(hes/explicit-simple-dash-a* (dmh ~'init))]

   ["dash-astar" `(da/implicit-dash-a* (dmh ~'init))]
   ["dash-astar-first" `(da/implicit-dash-a* (dmh ~'init) :choice-fn first)]
   ["dash-astar-ldfs" `(da/implicit-dash-a* (dmh ~'init) :search-strategy :ldfs)]
   ["dash-astar-hoc" `(da/implicit-dash-a* (dmh ~'init) :collect? :hierarchical)]
   ["dash-astar-nos" `(da/implicit-dash-a* (dmh ~'init) :abstract? false)]
   ["dash-astar-nods" `(da/implicit-dash-a* (dmh ~'init) :abstract? false :decompose? false)]

   ["dash-astar-sh-hoc" `(da/implicit-dash-a* (dmh ~'init)
                            :search-strategy :ao-global :choice-fn shallowest-dm
                            :collect? :hierarchical)]
   ["dash-astar-sh" `(da/implicit-dash-a* (dmh ~'init) 
                           :search-strategy :ao-global :choice-fn shallowest-dm)]
   ["dash-astar-sh-nos" `(da/implicit-dash-a* (dmh ~'init)
                           :search-strategy :ao-global :choice-fn shallowest-dm
                           :abstract? false)]
   ["dash-astar-sh-nods" `(da/implicit-dash-a* (dmh ~'init)
                           :search-strategy :ao-global :choice-fn shallowest-dm
                           :abstract? false :decompose? false)]])


(defn make-dm-exps [& [test]]
  (for [[pn pf] [["easy" `dm/make-random-discrete-manipulation-env]
                 ["hard" `dm/make-random-hard-discrete-manipulation-env]]
        [n f] dm-algs]
    [(str pn "_" n)
     [(fn [sz rep]
          (let [size (nth +dm-sizes+ sz)]
            (experiments/make-experiment
             (str pn "_" n "-" sz "-" rep)
             {:problem pn :alg n :size-i sz :size size :rep rep}
             'angelic.scripts.thesis
             `(~pf ~size ~rep)
             f
             ;nil 1
             10 3600
             512 nil ::ExpResult)))
      (count +dm-sizes+) +dm-reps+]]))

#_ (do (use 'angelic.scripts.thesis 'angelic.util.experiments 'angelic.util.cluster)
       (cluster-smart-runner (make-dm-exps) false (str *default-run-dir* "/thesis-dm/")))


(defn make-dm-exps2 [& [test]]
  (for [[pn pf] [["smaller" `dm/make-random-smaller-discrete-manipulation-env]]
        [n f] dm-algs]
    [(str pn "_" n)
     [(fn [sz rep]
          (let [size (nth +dm-sizes+ sz)]
            (experiments/make-experiment
             (str pn "_" n "-" sz "-" rep)
             {:problem pn :alg n :size-i sz :size size :rep rep}
             'angelic.scripts.thesis
             `(~pf ~size ~rep)
             f
             ;nil 1
             10 3600
             nil #_ 512 nil ::ExpResult)))
      (count +dm-sizes+) +dm-reps+]]))


#_ (do (use 'angelic.scripts.thesis 'angelic.util.experiments 'angelic.util.cluster) (cluster-smart-runner (make-dm-exps2) false (str *default-run-dir* "/thesis-dm3/")))


(comment ;; to run locally, if needed.
 (let [es (make-ns-exp-set)]
   (doseq [[i e] (indexed es)]
     (when (= (:alg (:parameters e)) :dash-a*)
       (run-experiment-set! es i (inc i))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;; DASH experiments ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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


(defn ddh [e] (dd/make-dash-hierarchy e (interpolating-heuristic 0.9 (:depth e))))

(def dd-algs
  [["dijkstra" `(textbook/uniform-cost-search ~'init true)]
   ["inv-dsh-ucs" `(hes/dsh-ucs-inverted (ddh ~'init))]
   ["optimistic-ah-astar" `(aha/optimistic-ah-a* (ddh ~'init) true)]
   ["dash-astar" `(da/implicit-dash-a* (ddh ~'init))]])


(def +dd-sizes+  10)
(def +dd-reps+  3)

(defn make-dd-exps [& [test]]
  (for [[pn pf] [["num"  (fn [s] [(+ 1 s) 3 3])]
                 ["size" (fn [s] [1 (+ 2 s) 3])] 
                 ["both" (fn [s] [(+ 1 s) (+ 2 s) 3])]]
        [n f] dd-algs]
    [(str pn "_" n)
     [(fn [sz rep]
        (let [[sps bits target-count :as args] (pf sz)]
            (experiments/make-experiment
             (str pn "_" n "-" sz "-" rep)
             {:problem pn :alg n :size-i sz :sps sps :bits bits :target-count target-count}
             'angelic.scripts.thesis
             `(dd/make-dash-env ~sps ~bits ~target-count)
             f
             ;nil 1
             10 3600
             512 nil ::ExpResult)))
      +dd-sizes+ +dd-reps+]]))

#_ (do (use 'angelic.scripts.thesis 'angelic.util.experiments 'angelic.util.cluster)
       (cluster-smart-runner (make-dd-exps) false (str *default-run-dir* "/thesis-dd/")))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn smart-results->dataset [smart-results combiner]
  (for [[_ results] smart-results
        size-results results
        :let [comb (combiner size-results)]
        :when (seq comb)]    
    (into {}
          (concat (apply clojure.set/intersection (map set size-results))
                  comb))))

(defn derive-median [c target-field source-field & [mapper]]
  (fn [s]
    (when-let [r (median-of c (map (if mapper (comp mapper source-field) source-field)
                                   (filter :ms s)))]
      {target-field r})))

(defn derive-median-multi [c target-field mapper]
  (fn [s]
    (when-let [r (median-of c (map mapper (filter :ms s)))]
      {target-field r})))

(def chart-opts
  {:term "dashed size 5.5,3.0 font 18"
   :key "out right center Left box lw 0.5 reverse width 0" #_"bottom right" #_"at 2.6, 445"})

(let [fl 1 bb 2 sa 3 na 4 ah 5 ex 6 da 7]
 (def alg-styles
   {:dijkstra            [fl 3  "UCS"]
    :astar               [fl 2  "A*"]

    :go-dfbb             [bb 3  "DFBB"]

    :sahtn               [sa 4  "SAHTN"]

    :h-ucs               [na 5  "H-UCS"]
    :dsh-ucs             [na 26  "DSH-LDFS"]
    :inv-dsh-ucs         [na 7  "DSH-UCS"]

    :optimistic-ah-astar [ah 8  "AH-A*-opt"]
    :strict-ah-astar     [ah 9  "AH-A*-strict"]
    :full-ah-astar       [ah 10 "AH-A*"]

    :explicit-ah-astar   [ex 11 "EXP-AH-A*-opt"]
    :explicit-dash-astar [ex 12 "EXP-DASH-A*"]

    :dash-astar          [da 13 "DASH-A*"]
    :dash-astar-first    [da 14 "DASH-A*-first"]
    :dash-astar-ldfs     [da 20 "DASH-A*-ldfs"]
    :dash-astar-hoc      [da 16 "DASH-A*-hog"]
    :dash-astar-nos      [da 3 "DAcH-A*"]
    :dash-astar-nods     [da 18 "DAxH-A*"]

    :dash-astar-sh       [da 5 "DASH-A*-sh"] 
    :dash-astar-sh-hoc   [da 16 "DASH-A*-sh-hog"]
    :dash-astar-sh-nos   [da 3 "DAcH-A*-sh"]
    :dash-astar-sh-nods  [da 18 "DAxH-A*-sh"]

    }))

(defn alg-title [a] (-> alg-styles a (nth 2)))
(defn alg-style [a]
  (let [[t c] (alg-styles a)]
    {:lw 3 :lt t :pt t :lc c}))

(def chart-dir "/Users/w01fe/Projects/phdthesis/graphs/")

(defn make-chart [ds algs field & [more-chart-opts derive pdf-file]]
  (util/assert-is (empty? (remove ds algs)))
  (let [sks (map alg-title algs)
        c   (-> ds first second first count)]
    (println "Medians of" c)
    (-> (smart-results->dataset
         (select-keys ds algs)
         (or derive
             (if (= field :secs)
               (derive-median c :secs :ms #(/ % 1000))
               (derive-median c field field))))
        (datasets/ds->chart
         [:alg] :size field
         (merge chart-opts more-chart-opts)
         (comp alg-style keyword first)
         (comp alg-title keyword first)
         (fn [arg] (sort-by #(util/position (:title %) sks) arg)))
        (#(if pdf-file (charts/plot % (str chart-dir pdf-file)) (charts/plot %))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Nav charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def ns-results
  (->> (str experiments/*default-run-dir* "thesis-ns2/")
       (experiments/read-smart-results (make-ns-exps) )
       (util/map-keys keyword)
       delay))

;; Skip: explicit-ah-astar explicit-dash-astar

#_(def ns-slow-algs [:go-dfbb :sahtn :dsh-ucs :inv-dsh-ucs :h-ucs :optimistic-ah-astar :strict-ah-astar :dijkstra :astar 
                   :full-ah-astar :dash-astar ;-ldfs 
                   ])

(def ns-slow-algs [:go-dfbb :sahtn :dsh-ucs :inv-dsh-ucs :h-ucs :optimistic-ah-astar :strict-ah-astar :dash-astar-nods :dijkstra :astar :dash-astar-first :dash-astar  :dash-astar-hoc :dash-astar-nos 
                   :full-ah-astar :dash-astar-ldfs 
                   ])

(def ns-fast-algs [:optimistic-ah-astar :strict-ah-astar
                   :dash-astar-nods :dijkstra :astar :dash-astar-first :dash-astar  :dash-astar-hoc :dash-astar-nos 
                   :full-ah-astar :dash-astar-ldfs ])


(defn make-ns-charts []
  (let [opts (fn [t yr]
               {:title (str "nav-switch - runtime - " t " algorithms")
                :xlabel "grid side length" :ylabel "runtime (s)"
                :xrange "[5:500]" :yrange yr})]
    (make-chart @ns-results ns-slow-algs :secs (opts "all" "[0:50]") nil "ns-slow.pdf")
    (make-chart @ns-results ns-fast-algs :secs (opts "faster" "[0:9]") nil "ns-fast.pdf")))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  DM charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn first-segment [^String s] (first (.split s "_")))
(defn rest-segments [^String s] (second (.split s "_")))

(def dm-results
  (->> (str experiments/*default-run-dir* "thesis-dm3/")
       (experiments/read-smart-results (make-dm-exps2))
       (group-by (comp keyword first-segment first))
       (util/map-vals (partial util/map-keys (comp keyword rest-segments)))
       delay))


;; leaving out :strict-ah-astar :full-ah-astar :explicit-ah-astar :dash-astar-nods :dash-astar-nos :dash-astar-hoc
;; :explicit-dash-astar :dash-astar-first

(def dm-alg-ord [:h-ucs :dijkstra :optimistic-ah-astar :sahtn :dsh-ucs
                 :dash-astar-sh-nods :inv-dsh-ucs :dash-astar :dash-astar-ldfs
                 :dash-astar-sh-nos :dash-astar-sh-hoc  :dash-astar-sh ])

(def dm-alg-ord2 [:h-ucs :dijkstra :optimistic-ah-astar 
                 :dash-astar-sh-nods :dash-astar-sh-nos :dash-astar :dash-astar-ldfs
                   :dash-astar-sh-hoc  :dash-astar-sh
                  :sahtn :dsh-ucs :inv-dsh-ucs
                  ])

(defn make-dm-charts []
  (make-chart
   (:smaller @dm-results) dm-alg-ord :secs
   {:ylog  "t" :xtics "1" :yrange "[0.4:1000]"
    :title (str "discrete manipulation - runtime") :xlabel "\\# of objects" :ylabel "runtime (s)"}
   nil "dm-runtime.pdf")
  (make-chart
   (:smaller @dm-results) dm-alg-ord2 :all-count
   {:ylog  "t" :xtics "1" :yrange "[100:1000000]"
    :title (str "discrete manipulation - description evaluations")
    :xlabel "\\# of objects" :ylabel "\\# of evaluations"}
   (derive-median-multi 5 :all-count #(+ (:opt-count %) (:next-count %)))
   "dm-evals.pdf"))


;; note: sahtn with dijkstra, not as described.
;; note: right now dfbb set to shuffle.
;; note: explicit algs effectively use different, more accurate heuristics.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; DD charts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn add-size [d]
  (into {}
        (for [[t ds] d]
          [t
           (util/map-vals
            (fn [os]
              (for [is os]
                (for [x is]
                  (let [si (:size-i x)]
                    (assoc x :size 
                           (case t
                                 :both (* (inc si) (inc (util/expt 2 (+ 2 si))))
                                 :num  (* 9 (inc si))
                                 :size (inc (util/expt 2 (+ 2 si)))))))))
            ds)])))

(def dd-results
  (->> (str experiments/*default-run-dir* "thesis-dd/")
       (experiments/read-smart-results (make-dd-exps))
       (group-by (comp keyword first-segment first))
       (util/map-vals (partial util/map-keys (comp keyword rest-segments)))
       add-size
       delay))


(defn make-dd-charts []
  (doseq [[t data] @dd-results]
    (let [[algs chart-opts]
          (case t
           :both [[:dijkstra :optimistic-ah-astar :inv-dsh-ucs :dash-astar]
                  {:xrange "[5:4500]" :yrange "[0.001:100]"}]
           :num  [[:dijkstra :optimistic-ah-astar :inv-dsh-ucs :dash-astar]
                  {:xrange "[9:100]" :yrange "[0.005:10]"}]
           :size [[:dijkstra :inv-dsh-ucs :optimistic-ah-astar :dash-astar]
                  {:xrange "[5:550]" :yrange "[0.001:1000]"}
                  ])]
      (make-chart
       data (or algs (keys data)) :secs
       (assoc chart-opts 
         :ylog  "t"  :xlog "t" ;:xrange "[5:500]"  :yrange "[0.01:100]"
         :title (str "bit-stash - runtime - scaling "
                     (case t :num "number of subproblems" :size "subproblem size" :both "both"))
         :xlabel "optimal solution length" :ylabel "runtime (s)")
       nil (str "dd-" (name t) "-log.pdf")
       )))
  (make-chart (:both @dd-results) [:dijkstra :optimistic-ah-astar :inv-dsh-ucs :dash-astar] :secs
              {:xrange "[0:4500]" :yrange "[0:100]"
               ;:xrange "[0:10000]" :yrange "[0:400]"
               :title (str "bit-stash - runtime - scaling both") :xlabel "optimal solution length" :ylabel "runtime (s)"}
              nil "dd-both.pdf"))

(defn make-all-charts []
  (make-ns-charts)
  (make-dm-charts)
  (make-dd-charts))


;; Note: right factoring is crucial! (hsould also sub-factor tla refs?)
;; hierarchical hurts here.










;;; old stuff

(comment
  (def dm-results
  (->> (str experiments/*default-run-dir* "thesis-dm/")
       (experiments/read-smart-results (make-dm-exps))
       (group-by (comp keyword first-segment first))
       (util/map-vals (partial util/map-keys (comp keyword rest-segments)))
       delay))
 ;; TODO: opt-count
 (defn make-dm-charts []
   (make-chart
    (:easy @dm-results) dm-alg-ord :secs
    {:ylog  "t"     ;:xlog "t" ;:xrange "[5:500]" :yrange "[0.01:100]"
     :title (str "discrete manipulation problems") :xlabel "\\# of objects" :ylabel "runtime (s)"})
   (make-chart
    (:hard @dm-results) dm-alg-ord :secs
    {:ylog  "t"     ;:xlog "t" ;:xrange "[5:500]" :yrange "[0.01:100]"
     :title (str "hard discrete manipulation problems") :xlabel "\\# of objects" :ylabel "runtime (s)"})))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; Testing Code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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


(defn worst-leaf [ss]
  (apply min-key (comp :min-leaf angelic.search.summary-graphs-newer/summary) ss))

(defn dm-test [& args]
  (let [e (apply dm/make-random-discrete-manipulation-env args)
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
            #_ ["strict-ah-a*" #(aha/strict-ah-a* h true)]
             #_["full-ah-a*" #(aha/full-ah-a* h true)]                                       

             #_["explicit-ah-a*" #(hes/explicit-simple-ah-a* h)]
             #_["explicit-dash-a*" #(hes/explicit-simple-dash-a* h)]

#_             ["nps-dash-a*" #(da/implicit-dash-a* h :propagate-subsumption? false)]
#_             ["ldfs-dash-a*" #(da/implicit-dash-a* h :search-strategy :ldfs)]
             ["dash-a*" #(da/implicit-dash-a* h)]
#_             ["dah-a*" #(da/implicit-dash-a* h :abstract? false)]
#_             ["ah-a*" #(da/implicit-dash-a* h :abstract? false :decompose? false)]                          
             ["first-dash-a*" #(da/implicit-dash-a* h :choice-fn first)]             
             ["shallowest-dash-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global
                          :choice-fn shallowest-dm)]
             ["shallowest-dah-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global :abstract? false
                          :choice-fn shallowest-dm)]
             ["shallowest-ah-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global :abstract? false :decompose? false
                          :choice-fn shallowest-dm)]             
             ["h-first-dash-a*" #(da/implicit-dash-a* h :collect? :hierarchical)]
             ["h-shallowest-dash-a*" #(da/implicit-dash-a*
                          h :search-strategy :ao-global :collect? :hierarchical
                          :choice-fn shallowest-dm)]
             
             ]]
      (println (pad-right n 20)
               (update-in (run-timed f) [0 0] count)))))



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
             ["dash-a*" #(da/implicit-dash-a* h8i :choice-fn flast-choice)]
             #_["dash-a*" #(da/implicit-dash-a* h8i :collect? :hierarchical)]
             #_["dash-a*" #(da/implicit-dash-a* h8i :choice-fn flast-choice :collect? :hierarchical)]                          
             #_ ["1.0-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 1) true)]
             #_ ["0.9-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 0.9) true)]
             #_ ["0.8-a*" #(textbook/a*-search e (partial dd/simple-dash-heuristic e 0.8) true)]
             
             #_ ["1.0-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 1))  true)]
             #_ ["0.9-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 0.9)) true)]
             #_ ["0.8-opt-ah-a*"
              #(aha/optimistic-ah-a* (dd/make-dash-hierarchy e (constantly 0.8))  true)]
             ["0.8i-opt-ah-a*" #(aha/optimistic-ah-a* h8i true)]

             ["inv-dsh-ucs" #(hes/dsh-ucs-inverted h8i)]
             
             #_ ["dash-a*" #(da/implicit-dash-a* h8i)]
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


