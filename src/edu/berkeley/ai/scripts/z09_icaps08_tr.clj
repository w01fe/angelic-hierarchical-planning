(ns edu.berkeley.ai.scripts.z09-icaps08-tr
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets]]
           [edu.berkeley.ai.domains [strips :as strips] [nav-switch :as nav-switch] [warehouse :as warehouse]]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-valuations :as dv]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies [strips-hierarchies :as strips-hierarchies] 
	    [abstract-lookahead-trees :as alts] [offline-algorithms :as offline]
	    [online-algorithms :as online]]
	   [edu.berkeley.ai.scripts.experiments :as experiments]
	   )
 )

(def *run-folder* "/Users/jawolfe/Projects/reports/09-icaps08-tr/results/")
	
(def *warehouse-args* 
     [[3 4 [2 3] true {0 '[a] 2 '[c baz]} nil '[[c a]]]
      [4 4 [2 3] true {0 '[a] 2 '[c baz]} nil '[[baz c a]]]
      [4 4 [2 3] true {0 '[a] 2 '[c baz]} nil '[[a baz c table3]]]
      [4 8 [2 4] true {0 '[a] 2 '[c baz]} nil '[[c baz table3]]]
      [4 8 [2 3] true {0 '[a] 2 '[c baz]} nil '[[a c table1]]]
      [4 6 [2 4] true {0 '[a] 2 '[c baz]} nil '[[c baz table3]]]
					; my instances
      [2 2 [1 1] false {0 '[a]} nil ['[a table1]]]
      [3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]]]
      [3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]]
      [7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]]]
      [5 4 [1 2] false {0 '[a b] 1 '[c] 2 '[d e] 3 '[f]} nil '[[a d table1]]]

      [4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]]
      [10 4 [1 2] false {0 '[a] 9 '[c b]} nil ['[a c table1]]]
      [20 4 [1 2] false {0 '[a] 19 '[c b]} nil ['[a c table1]]]
      [4 20 [1 2] false {0 '[a] 3 '[c b]} nil ['[a c table1]]]
      [10 20 [1 2] false {0 '[a] 9 '[c b]} nil ['[a c table1]]]
      [20 20 [1 2] false {0 '[a] 19 '[c b]} nil ['[a c table1]]]

      [4 4 [0 3] false {0 '[a c] 3 '[e g]} nil '[[a e table1] [c g table3]]]
      [4 4 [0 3] false {0 '[a c] 3 '[e g]} nil '[[a e table1] [g c table3]]]
      [4 10 [0 3] false {0 '[a c] 3 '[e g]} nil '[[a e table1] [g c table3]]]
      [6 5 [0 4] false {0 '[a c] 3 '[e g]} nil '[[a e table1] [c g table4]]]

      ;; infeasible: TODO; look for more.  ICAPS should be better, but it's not (pruning)? ...
      [3 6 [0 3] false {0 '[a c] 2 '[e g]} nil '[[a e table0] [g c table2]]]
      [4 4 [1 3] false {0 '[a b c] 1 '[x d] 2 '[e g] } nil '[[a e table0] [g c table2]]]
      ])


(defn get-ns-form [size switches run]
  `(strips/constant-predicate-simplify 
    (apply nav-switch/make-nav-switch-strips-env 
	   ~(nav-switch/make-random-nav-switch-args-code size switches run))))

(defn get-warehouse-form [args]
  `(strips/constant-predicate-simplify
    (apply warehouse/make-warehouse-strips-env '~args)))

(defn get-env-init-form [m]
  (condp = (:domain m)
    :nav-switch (get-ns-form (:size m) (if (integer? (:switches m)) (:switches m) (int (Math/ceil (* (:switches m) (:size m) (:size m))))) (:run m))
    :warehouse  (get-warehouse-form (nth *warehouse-args* (:instance-num m)))))

(defn get-hierarchy-init-form [m env-form]
  (condp = (:type m)
    :hierarchy       `(hierarchies/get-hierarchy ~(:hierarchy m) ~env-form)
    :flat-hierarchy  `(let [env# ~env-form] (strips-hierarchies/get-flat-strips-hierarchy env# (~(:heuristic m) env#)))
    :strips          env-form))

(defn get-alt-args [m]
  {:graph? (:graph? m) :ref-choice-fn (:choice-fn m) :recheck-graph? (:recheck-graph? m) :cache? (get m :cache? true)
   :opt-valuation-class :edu.berkeley.ai.angelic.dnf-valuations/DNFOptimisticSimpleValuation
   :pess-valuation-class :edu.berkeley.ai.angelic.dnf-valuations/DNFPessimisticSimpleValuation})

(defn get-node-init-form [m hierarchy-form]
  (cond (= (util/safe-get m :algorithm) :ahlrta-star)
	  hierarchy-form
        (contains? #{:hierarchy :flat-hierarchy} (:type m))
	  `(alts/alt-node ~hierarchy-form ~(get-alt-args m)) 
	(= :strips (:type m))
	  `(let [env# ~hierarchy-form] (search/ss-node env# (~(:heuristic m) env#)))))

(defn get-init-form [m]
  (get-node-init-form m (get-hierarchy-init-form m (get-env-init-form m))))

(defn get-solution-form [m]
  `(envs/solution-name (apply ~(:algorithm-fn m) ~'init 
    ~(if (= (util/safe-get m :algorithm) :ahlrta-star)
	 [(util/safe-get m :max-steps) (util/safe-get m :max-refs) `'~(util/safe-get m :high-level-hla-set)
	  (get-alt-args m) (util/safe-get m :max-primitives) `'~(util/safe-get m :ref-level-map)]
       (:algorithm-args m)))))

(defn make-icaps-tr-experiment-set [name max-seconds arg-spec]
  (experiments/make-experiment-set name
    arg-spec get-init-form get-solution-form
    'edu.berkeley.ai.scripts.z09-icaps08-tr 10
     max-seconds 512 false experiments/*planning-experiment-result*))


(defn make-offline-experiment-set []
  (make-icaps-tr-experiment-set "offline" 10000
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]] 
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [5 10 20 50 100 200 500]]
		     [:switches [20]]
		     [:run      [1 2 3]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-nl-improved*]]
		     [:instance-num (vec (range 23))]
		    ]]]]
      [:union  
         [:product 
            [:type      [:strips]]
	    [:algorithm [] [[:a-star-graph [:algorithm-fn [`textbook/a-star-graph-search]]]]]]
         [:product
	    [:type      [:flat-hierarchy]]
            [:graph?    [:full]]
	    [:recheck-graph? [true]]
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]]]]
	 [:product
	    [:type      [:hierarchy]]
            [:graph?    [:full]]
	    [:recheck-graph? [true]]
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]
			    [:ahss         [:algorithm-fn ['offline/ahss-search]]]]]]]]))

(defonce *offline* nil)

(defn read-offline-results []
    (let [ww-order [6 7 0 8 1 21 2 5 22 11 3 9 12 4 13 14 15 10 17 16 18]] ;20 19 ]]  
      (def *offline*
	 (doall 
	 (map (fn [m] (into {} (assoc (if (= :warehouse (:domain m)) 
			       (update-in m [:instance-num] #(util/position % ww-order)) 
			       m)
			:printed nil :output [nil (second (:output m))]))) 
	      (experiments/experiment-set-results->dataset 
	       (experiments/read-experiment-set-results (make-offline-experiment-set) 
							*run-folder*)))))))
; 136 and 148 ran out of memory hard.  
; These are ww instances 3 and 16, with a-star-graph-search.  

; Hierarchy ran out of memory (soft) on instance 20.  

; All three runs of flat-hierarchy ran out of time (soft) on 500x500 problems.
 
; Flat hierarchy ran out of memory (soft) on instance 21 of WW, and 1 200-run of NS.

; flat and flat-hierarchy show discrepancy only in plan count, since flat-heirarchy 
; actually produces the primitive plans while flat leaves them implicit.

(defn make-offline-charts 
  ([] (make-offline-charts "/Users/jawolfe/Desktop/new-charts/"))
  ([dir] 
   (doseq [[y-axis y-label file-suffix]
	   [[:ms "Solution Time (ms)" "time"]
	    [:ref-count "# of Refinements" "refs"]
	    [:plan-count "# of Plans Evalauted" "plans"]]]
    (charts/plot (datasets/ds->chart 
      (filter (datasets/ds-fn [domain hierarchy algorithm ms] 
			      (and ms (= domain :warehouse) (not (= algorithm :a-star-graph)))) 
	      *offline*) 
      [:type :graph? :ref-choice :algorithm ] 
      :instance-num y-axis
      {:term "solid dashed size 3,2"
       :ylog "t" :key "12,100000" :yrange "[10:200000]" :xlabel "Problem Number" :ylabel y-label
       :title "Offline Warehouse World" 
       } 
      (let [c (util/counter-from 0)]
	(fn [& args] (let [v ([1 2 3] (c))]  {:lw 3 :pt v :lt v})))
;      (constantly {:lw 4 :pt [2 3 4]})
      (fn [[type graph ref-choice alg]]
	(cond (= alg :ahss) "AHSS" (= type :hierarchy) "AHA*" :else "Graph A*"))
      identity)
     (str dir "offline-ww-" file-suffix ".pdf"))
    (charts/plot (datasets/ds->chart 
      (filter #(< (:ref-count %) 5.0e9) 
        (datasets/ds-summarize 
	  (filter (datasets/ds-fn [type algorithm domain] 
				  (and (= domain :nav-switch) (not (= algorithm :a-star-graph)))) 
	    (map #(if (:ms %) % (assoc % :plan-count 1.0e10 :ref-count 1.0e10 :ms 1.0e10)) 
		 *offline*)) 
	  [:type :graph? :ref-choice :algorithm :switches :size] 
	  [[:ref-count  (fn [& args] (when (every? first args) (util/median (map second args)))) 
	    (fn [m] [(:run m) (y-axis m)])]]))  
      [:type :graph? :ref-choice :algorithm :switches]
      :size :ref-count 
      {:term "solid dashed size 3,2"
       :ylog "t" :xlog "t" :key "45,100000"
       :title "Offline Nav Switch"
       :xlabel "Board size (per side)" :ylabel y-label 
       :xrange "[5:1000]" :yrange "[50:200000]"} 
      (let [c (util/counter-from 0)]
	(fn [& args] (let [v ([1 2 3] (c))]  {:lw 3 :pt v :lt v})))
;      (constantly {:lw 4})
      (fn [[type graph ref-choice alg]]
	(cond (= alg :ahss) "AHSS" (= type :hierarchy) "AHA*" :else "Graph A*"))
      identity)
     (str dir "offline-nav-" file-suffix ".pdf")))      
   ))
     






(defn make-online-experiment-set []
  (make-icaps-tr-experiment-set "online" 1000000
    [:product
     [:max-primitives [nil]]
     [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]]
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [100 500]]
		     [:switches [20]] ; 0.10]]
		     [:run      [1 2 3]]
;		     [:run      [1]]
		     [:high-level-hla-set ['#{act go}]]
		     [:ref-level-map [nil]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-nl-improved*]]
		     [:instance-num (vec (range 21))]
		     [:high-level-hla-set ['#{act move-blocks}]]
		     [:ref-level-map [nil]]
		    ]]]]
     [:algorithm [:ahlrta-star]]
     [:algorithm-fn [`online/ahlrta-star-search]]
     [:max-steps [10000]]
     [:max-refs  [10 20 50 100 200 300 400 500 750 1000 1500 2000 3000 4000 5000]]
;     [:max-refs  [10 30 100 300 1000 ]]
;     [:max-refs  [10 ]]
     [:type [] [[:flat-hierarchy
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]
		[:hierarchy 
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]]]
     [:graph?         [:full]]
     [:recheck-graph? [true]]
     ]))

(defonce *online* nil)

(defn read-online-results []
  (def *online* 
      (doall 
       (map #(into {} (assoc % :printed nil :output [nil (second (:output %))] ))
	    (cons (assoc (:parameters (nth (make-online-experiment-set) 679))
		    :output [nil -10000] :ms 100000)
	    (experiments/experiment-set-results->dataset 
	     (experiments/read-experiment-set-results (make-online-experiment-set) 
						      *run-folder*)))))))

(defn read-full-online-results []
  (def *online* 
      (doall 
       (map #(into {} (assoc % :printed nil  ))
	    (cons (assoc (:parameters (nth (make-online-experiment-set) 679))
		    :output [nil -10000] :ms 100000)
	    (experiments/experiment-set-results->dataset 
	     (experiments/read-experiment-set-results (make-online-experiment-set) 
						      *run-folder*)))))))

; 10 runs failed hard by exceeding 1-day time limit:
 ; flat-hierarchy with 3k, 4k, 5k refs on 500x500, all 3 runs
 ; hierarchy, instance 16, 1000 refs per step.

; No soft time/memouts.  

; Way Too hard:       19  
; Maybe too hard: 20, 18, 10?
; Just right:     17, 16, 15, 14, 13, 4, 3
; Maybe too eash: 12, 11, 9, 5, 2
; Too easy:       8, 7, 6, 1, 0

; Both converged before 100: way too easy
; Both converged before 1000: too eash
; Neither converged by 5000: too hard.
; Mostly living at 10,000: way too hard

; Use geometric mean to preserve ratios.

; (doseq [m (filter #(= (map % [:size :type]) [100 :hierarchy]) *online*)] (println (:max-refs m) (:ref-count m) (/ (:ms m) (:ref-count m))))
; ... shows runtime per ref is comparable for flat and hierarchical on both domains.

(defn make-online-charts 
  ([] (make-online-charts "/Users/jawolfe/Desktop/new-charts/"))
  ([dir] 
   ; Warehouse
   (doseq [[combiner-fn combiner-name]
 	     [#_[util/mean "mean"] 
	      [util/geometric-mean "geo-mean"] 
	      #_[(fn [& args] (util/median args)) "median"]]
	   [subset subset-name]
	     [[[17, 16, 15, 14, 13, 4, 3] "middle"]
	      #_[[17, 16, 15, 14, 13, 4, 3, 20, 18, 10, 12, 11, 9, 5, 2] "most"]
	      #_[(range 21) "all"]]]
     (charts/plot (datasets/ds->chart 
       (datasets/ds-summarize 
	 (datasets/ds-derive (datasets/ds-fn [output ] (- (or (second output) -10000))) 
	   (filter (datasets/ds-fn [ms instance-num] (and ms ((set subset) instance-num))) 
	     (filter (datasets/ds-fn [domain] (= domain :warehouse)) *online*)) 
	   :cost) 
	 [:type :graph? :ref-choice :algorithm :switches :size :max-refs] 
	 [[:cost combiner-fn (datasets/ds-fn [cost] cost)]]) 
       [:algorithm :type :ref-choice] 
       :max-refs :cost 
       {:term "solid dashed size 3,2" :xrange "[0:5000]" :yrange "[70:3000]" :key "3000, 1800"  
	:title (str "Online Warehouse World") :ylog "t"
	:xlabel "Allowed refinements per env step" 
	:ylabel "Cost to reach goal (avg of 7 instances)"} 
      (let [c (util/counter-from 0)]
	(fn [& args] (let [v ([1 2 3] (c))]  {:lw 3 :pt v :lt v})))
;      (constantly {:lw 4})
      (fn [[alg type ref-choice]]
	(cond (= alg :ahss) "AHSS" (= type :hierarchy) "AHLRTA*" :else "LRTA*"))
      identity)
        "/Users/jawolfe/Desktop/new-charts/online-ww.pdf"))

   ; Nav Switch
   (doseq [[sz keyloc maxx] [[100 "3500, 500" 5000] [500 "1800, 4500" 2000]]]
    (charts/plot (datasets/ds->chart 
      (datasets/ds-summarize 
        (datasets/ds-derive (datasets/ds-fn [output ] (- (or (second output) -20000))) 
	  (filter (datasets/ds-fn [ms size] (and ms (= size sz))) 
	    (filter (datasets/ds-fn [domain] (= domain :nav-switch)) *online*)) 
	  :cost) 
	[:type :graph? :max-refs :ref-choice :algorithm :switches :size] 
	[[:cost (fn [& args] (apply util/geometric-mean args)) (datasets/ds-fn [cost] cost)]]) 
      [:algorithm :type :ref-choice] 
      :max-refs :cost 
      {:term "solid dashed size 3,2" :xrange (str "[10:" maxx "]")
       ;:xlog "t" 
       :key keyloc 
       :title (str "Online Nav Switch " sz "x" sz ", 20 switches") 
       :xlabel "Allowed refinements per env step"
       :ylabel "Cost to reach goal (avg of 3 random instances)" } 
;      (constantly {:lw 4})
      (let [c (util/counter-from 0)]
	(fn [& args] (let [v ([1 2 3] (c))]  {:lw 3 :pt v :lt v})))
      (fn [[alg type ref-choice]]
	(cond (= alg :ahss) "AHSS" (= type :hierarchy) "AHLRTA*" :else "LRTA*"))
      identity)
     (str dir "online-nav-" sz ".pdf")))))      






(defn make-offline-hfs-experiment-set []
  (make-icaps-tr-experiment-set "offline-hfs" 10000
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
;		     [:size [5]]
;		     [:switches [1]]
;		     [:run [1]]
		     [:size     [5 10 20 50 100 200 500]]
		     [:switches [20]]
		     [:run      [1 2 3]]
		     ]]
		   [:warehouse
		    [:product
		     [:hierarchy [`warehouse/*warehouse-hierarchy-nl-improved*]]
;		     [:instance-num (vec (range 2))]
		     [:instance-num (vec (range 23))]
		    ]]]]
     [:type      [:hierarchy]]
     [:graph?    [false]]
     [:cache?    [false]]
     [:recheck-graph? [false]]
     [:ref-choice-fn [] [[:first-maximal [:choice-fn [`(alts/make-first-maximal-choice-fn 
							~''{act 10 move-blocks 9 move-block 8 move-to 7
							  navigate 6 go 5 nav 4})]]]]]
     [:algorithm [] [[:hfs        [:algorithm-fn ['offline/hierarchical-forward-search]]]]]]))

(defonce *offline-hfs* nil)

(defn read-offline-hfs-results []
    (let [ww-order [6 7 0 8 1 21 2 5 22 11 3 9 12 4 13 14 15 10 17 16 18]] ;20 19 ]]  
      (def *offline-hfs*
	 (doall 
	 (map (fn [m] (into {} (assoc (if (= :warehouse (:domain m)) 
			       (update-in m [:instance-num] #(util/position % ww-order)) 
			       m)
			:printed nil :output [nil (second (:output m))]))) 
	      (experiments/experiment-set-results->dataset 
	       (experiments/read-experiment-set-results (make-offline-hfs-experiment-set))))))))


; HFS can only solve Nav-switch problems up to size 20, 5 easiest warehouse world problems (0-4) without running out of memory.
; 







; More online nav instances, for posterity

(defn make-extended-online-experiment-set []
  (make-icaps-tr-experiment-set "online-extra-nav" 1000000
    [:product
     [:max-primitives [nil]]
     [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]]
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [100 500]]
		     [:switches [20]] ; 0.10]]
		     [:run      [1 2 3 4 5 6 7 8 9 10]]
		     [:high-level-hla-set ['#{act go}]]
		     [:ref-level-map [nil]]
		     ]]]]
     [:algorithm [:ahlrta-star]]
     [:algorithm-fn [`online/ahlrta-star-search]]
     [:max-steps [10000]]
     [:max-refs  [10 20 50 100 200 300 400 500 750 1000 1500 2000 3000 4000 5000]]
     [:type [] [[:flat-hierarchy
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]
		[:hierarchy 
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]]]
     [:graph?         [:full]]
     [:recheck-graph? [true]]
     ]))














(comment 
  
; navigateless first-gap nil-max-prims seems best for ww

; scouting out ww
(doseq [ i (range 4 5) max-prims [nil 5]]  (plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives hierarchy ref-choice] (and ms  (= instance-num i) (= max-prims max-primitives) (= (count (str hierarchy)) 64) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:algorithm :type :ref-choice] :max-refs :cost {:ylog "t" :xlog "t" :key "1000, 6000" :xlabel (str i)} {})))

(doseq [ i (range 21)]  (plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num ] (and ms  (= instance-num i))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:hierarchy :ref-choice :algorithm :type :ref-choice] :max-refs :cost {:ylog "t" :xlog "t" :key "1000, 100" :xlabel (str i )} {})))

"[18? 17.0 16 15 14* 13 12* 9* 8-6e 4* 2* 1/0e]"
 

;; Average of selected instances
(plot (ds->chart (ds-summarize (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives] (and ms  (#{17 16 15 14 13 12 11 10  4 3 2 9 5} instance-num) (nil? max-primitives) )) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:type :graph? :ref-choice :algorithm :switches :size :max-refs] [[:cost mean (ds-fn [cost] cost)]]) [:algorithm :type :ref-choice] :max-refs :cost { :xrange "[0:5000]" :key "5000, 2000"  :title "Warehouse world - averaged over 13 instances" :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal"} {} ) #_ "/Users/jawolfe/Desktop/new-charts/online-ww.pdf")


; With other choices.
(plot (ds->chart (ds-summarize (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives hierarchy ref-choice] (and ms  (#{16 17 15 14 13 12 11 10  4 3 2 9 5} instance-num) (nil? max-primitives) )) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:type :graph? :ref-choice :hierarchy :algorithm :switches :size :max-refs] [[:cost mean (ds-fn [cost] cost)]]) [ :hierarchy :algorithm :type :ref-choice ] :max-refs :cost { :xrange "[0:5000]" :key "5000, 2000"  :title "Warehouse world - averaged over 13 instances" :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal"} {} ) "/Users/jawolfe/Desktop/new-charts/online-ww.pdf")


; Slides friendly
 (plot (ds->chart (ds-summarize (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives hierarchy ref-choice] (and ms  (#{18 17 15 14 13 12 11 10  4 3 2 9 5} instance-num) (nil? max-primitives) (= (count (str hierarchy)) 64) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:type :graph? :ref-choice :algorithm :switches :size :max-refs] [[:cost mean (ds-fn [cost] cost)]]) [:algorithm :type :ref-choice] :max-refs :cost {:term " solid color size 3,2" :xrange "[0:3000]" :key "2500, 2000"  :title "Online Warehouse World" :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal (average over 13 instances)"} (constantly {:lw 4}) (fn [[alg type ref]] (if (= type :hierarchy) "AHLRTA*" "LRTA*"))) "/Users/jawolfe/Desktop/new-charts/online-ww-slides.pdf")



; scouting out nav
(doseq [sz [100 500] sw [0.001] rn [1 2 3] ]  (plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [run ms size switches max-primitives hierarchy ref-choice] (and ms (= run rn) (= size sz) (= switches sw) (nil? max-primitives) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:algorithm :type :ref-choice] :max-refs :cost { :xlog "t" :key "7000, 6000" :xlabel (str sz "x" sz " - " sw)} {})))


; single 500x500 - 0.001 
(plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [run ms size switches max-primitives hierarchy ref-choice] (and ms (= run 3) (= size 500) (= switches 0.001) (nil? max-primitives) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:algorithm :type :ref-choice] :max-refs :cost { :yrange "[0:3000]" :xlog "t" :key "100, 1500" :title (str "Nav Switch 500x500 - 250 switches") :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal"} {}) "/Users/jawolfe/Desktop/new-charts/online-nav-500.pdf")

; slides
(plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [run ms size switches max-primitives hierarchy ref-choice] (and ms (= run 3) (= size 500) (= switches 0.001) (nil? max-primitives) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:algorithm :type :ref-choice] :max-refs :cost { :term " solid color size 3,2" :yrange "[0:3000]" :xrange "[10:500]" :key "300, 1500" :title (str "Online Nav Switch 500x500 - 250 switches") :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal"} (constantly {:lw 4}) (fn [[alg type ref]] (if (= type :hierarchy) "AHLRTA*" "LRTA*"))) "/Users/jawolfe/Desktop/new-charts/online-nav-500-slides.pdf")

; 100x100 - 0.001 - averaged over 3
(plot (ds->chart (ds-summarize (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [run ms size switches max-primitives hierarchy ref-choice] (and ms (= size 100) (= switches 0.001) (nil? max-primitives) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:type :graph? :max-refs :ref-choice :algorithm :switches :size] [[:cost mean (ds-fn [cost] cost)]]) [:algorithm :type :ref-choice] :max-refs :cost { :xlog "t" :key "5000, 600" :title "Nav Switch 100x100 - 10 switches - averaged over 3 instances" :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal" :yrange "[0:600]"} {}) "/Users/jawolfe/Desktop/new-charts/online-nav-100.pdf")



  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -20000))) (filter (ds-fn [ms instance-num max-primitives ref-level-map] (and ms (not ref-level-map) (= instance-num 9) (= max-primitives 5))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:algorithm :type :ref-choice ] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {})) 
 
  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -20000))) (filter (ds-fn [ms size max-primitives ref-level-map] (and ms (not ref-level-map)  (not max-primitives) (= size 500))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:algorithm :type :ref-choice ] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {}))

  )





















(comment 
; Warehouse world  
 (plot (ds->chart (filter (ds-fn [domain hierarchy algorithm ms] (and ms   (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm ] :instance-num :ms {:ylog "t" :key "12,100000" :yrange "[10:100000]" :xlabel "Problem number" :ylabel "ms solution time"} {})  "/Users/jawolfe/Desktop/new-charts/offline-ww-time.pdf")

   (plot (ds->chart (filter (ds-fn [domain hierarchy algorithm ms] (and ms (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm ] :instance-num :ref-count {:ylog "t" :key "12,100000" :yrange "[10:100000]" :xlabel "Problem number" :ylabel "# refinemens"} {})  "/Users/jawolfe/Desktop/new-charts/offline-ww-refs.pdf")

   (plot (ds->chart (filter (ds-fn [domain hierarchy algorithm ms] (and ms  (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm ] :instance-num :plan-count {:ylog "t" :key "12,100000" :yrange "[10:100000]" :xlabel "Problem number" :ylabel "# plans evaluated"} {})  "/Users/jawolfe/Desktop/new-charts/offline-ww-plans.pdf")


; Nav-switch, mean
(plot (ds->chart (ds-summarize (filter (ds-fn [ms type algorithm domain] (and ms (= domain :nav-switch))) *offline*) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (apply mean (map second args)))) (ds-fn [run plan-count] [run plan-count])]])  [:type :graph? :ref-choice :algorithm :switches] :size :plan-count {:ylog "t" :xlog "t" :key "45,1000000" :xlabel "Board size (per side)" :ylabel "Number of plans evaluated" :xrange "[5:1000]" :yrange "[50:1000000]"} {}) "/Users/jawolfe/Desktop/new-charts/offline-nav-plans.pdf")

; proper, with median
(plot (ds->chart (filter #(< (:ref-count %) 5.0e9) (ds-summarize (filter (ds-fn [type algorithm domain] (and (= domain :nav-switch))) (map #(if (:ms %) % (assoc % :plan-count 1.0e10 :ref-count 1.0e10 :ms 1.0e10)) *offline*)) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (median (map second args)))) (ds-fn [run plan-count] [run plan-count])]]))  [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:ylog "t" :xlog "t" :key "45,1000000" :xlabel "Board size (per side)" :ylabel "Number of plans evaluated" :xrange "[5:1000]" :yrange "[50:1000000]"} {}) "/Users/jawolfe/Desktop/new-charts/offline-nav-plans.pdf")

; Refinements
(plot (ds->chart (filter #(< (:ref-count %) 5.0e9) (ds-summarize (filter (ds-fn [type algorithm domain] (and (= domain :nav-switch))) (map #(if (:ms %) % (assoc % :plan-count 1.0e10 :ref-count 1.0e10 :ms 1.0e10)) *offline*)) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (median (map second args)))) (ds-fn [run ref-count] [run ref-count])]]))  [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:ylog "t" :xlog "t" :key "45,1000000" :xlabel "Board size (per side)" :ylabel "Number of refinements" :xrange "[5:1000]" :yrange "[10:1000000]"} {}) "/Users/jawolfe/Desktop/new-charts/offline-nav-refs.pdf")



; slides
(plot (ds->chart (ds-summarize (filter (fn [m] (and (contains? #{:full nil} (:graph? m)) (= (:switches m) 20) (contains? #{:first-gap nil} (:ref-choice m)))) (filter (ds-fn [type algorithm domain] (and (= domain :nav-switch) (#{:strips :hierarchy} type) (#{:aha-star :a-star-graph} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (apply mean (map second args)))) (ds-fn [run plan-count] [run plan-count])]])  [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:term " solid color size 3,2" :ylog "t" :xlog "t" :key "70,600000" :xlabel "World size (per side)" :ylabel "Number of plans evaluated (avg. of 3 instances)" :xrange "[5:1000]" :yrange "[50:1000000]" :title "Offline Optimal Nav-Switch (20 switches)"} (constantly {:lw 4}) (fn [[type graph? ref-choice algorithm switches]] (if (= type :hierarchy) "AHA*"  "A* Graph Search")) #(sort-by first %) ) "/Users/jawolfe/Desktop/new-charts/offline-nav-slides.pdf")




  
  )