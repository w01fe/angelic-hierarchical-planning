(ns edu.berkeley.ai.scripts.z09-aij
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
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

; hfs won't work with road trip ..... (shoudl now?)

; TODO: check out simple vs. full valuations.

; Need to configure ref-choice-fns, etc.

(defn make-09-aij-offline-experiment-set []
  (experiments/make-experiment-set "09-aij-offline"
    (experiments/parameter-set-tuples 
     '[:product 
       [:algorithm [;offline/hierarchical-forward-search
		     offline/aha-star-search
		     offline/ahss-search]]
       [:ref-choice [alts/first-choice-fn
		      ; alts/icaps-choice-fn
		      ]]
       [:domain     []
	[[warehouse/make-warehouse-strips-env [:args ['[3 4 [1 2] false {0 [b a] 2 [c]} nil [[a b c]]]]]]
	 [nav-switch/make-nav-switch-strips-env [:args ['[10 10 [[2 2]] [0 9] false [9 0]]]]]]]]
     (fn [m] #_ (println m) `(alts/alt-node (strips-hierarchies/get-flat-strips-hierarchy (strips/constant-predicate-simplify (apply ~(:domain m) ~(:args m))))
			~{:ref-choie-fn (:ref-choice m)}))
     (fn [m] #_ (println m) `(envs/solution-name (~(:algorithm m) ~'init))))
    'edu.berkeley.ai.scripts.z09-aij
    nil
    20
    512
    nil
    experiments/*planning-experiment-result*))
	
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

;(defn get-ns-args [size switches run )

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
  {:graph? (:graph? m) :ref-choice-fn (:choice-fn m) :recheck-graph? (:recheck-graph? m)
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

(defn make-aij-experiment-set [name max-seconds arg-spec]
  (experiments/make-experiment-set name
    arg-spec get-init-form get-solution-form
    'edu.berkeley.ai.scripts.z09-aij 10
     max-seconds 512 false experiments/*planning-experiment-result*))

; TODO: use simple valuations?!
; TODO: investigate AHLRTA* variations, ref-choice, etc.

(defn make-offline-experiment-set []
  (make-aij-experiment-set "offline-test" 10000
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]] 
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [5 10 50 100 500]]
		     [:switches [1 5 20 0.01 0.03 0.10]]
		     [:run      [1 2 3]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved* `warehouse/*warehouse-hierarchy-nl-improved*]]
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
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
			     [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]
			    [:ahss         [:algorithm-fn ['offline/ahss-search]]]]]]]]))
	 
(comment 
  ; All algorithms ran out of memory (hard) on problem 16. 
  (let [ww-order [6 0 7 8 1 21 2 5 22 11 3 9 12 4 13 14 15 10 17 18 20 19 16]]  
    (def *offline* 
	 (map (fn [m] (if (= :warehouse (:domain m)) 
			(update-in m [:instance-num] #(position % ww-order)) 
			m)) 
	      (experiment-set-results->dataset (read-experiment-set-results (make-offline-experiment-set) "/Users/jawolfe/Desktop/")))))

  (plot (ds->chart (filter (ds-fn [type domain] (and (= type :strips) (= domain :warehouse))) *offline*) [] :instance-num :ref-count {:ylog "t"} {}))
 
; offline-ww
  (plot (ds->chart (filter (ds-fn [domain hierarchy algorithm ms] (and ms (#{:aha-star :ahss} algorithm) (= (count (str hierarchy)) 67) (= domain :warehouse))) (filter #_(constantly true)  #(= (:ref-choice %) :first-gap) *offline*)) [:type :graph? :ref-choice :algorithm ] :instance-num :plan-count {:ylog "t" :key "12,100000" :yrange "[10:100000]" :xlabel "Problem number" :ylabel "# plans evaluated"} {}) "/Users/jawolfe/Desktop/new-charts/offline-ww.pdf")

; offline-nav
(plot (ds->chart (ds-summarize (filter (fn [m] (and (contains? #{:full nil} (:graph? m)) (= (:switches m) 20) (contains? #{:first-gap nil} (:ref-choice m)))) (filter (ds-fn [type algorithm domain] (and (= domain :nav-switch) (#{:strips :hierarchy} type) (#{:aha-star :a-star-graph} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (apply mean (map second args)))) (ds-fn [run plan-count] [run plan-count])]])  [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:ylog "t" :xlog "t" :key "45,1000000" :xlabel "Board size (per side)" :ylabel "Number of plans evaluated" :xrange "[5:1000]" :yrange "[50:1000000]"} {}) "/Users/jawolfe/Desktop/new-charts/offline-nav.pdf")

  (plot (ds->chart (filter (ds-fn [domain ms] (and ms (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "8,100000" :yrange "[10:100000]"} {}))

(plot (ds->chart (filter (ds-fn [algorithm domain timeout? memout?] (and (not timeout?) (not memout?) (= domain :warehouse) (contains? #{:aha-star :a-star-graph} algorithm))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "22,200" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:100000]"} {}) #_ "/Users/jawolfe/Desktop/charts/optimal-ww-refs.pdf")

(plot (ds->chart (filter (fn [m] (contains? #{nil :full} (:graph? m))) (filter (ds-fn [algorithm domain ms] (and ms (= domain :warehouse) (contains? #{:aha-star :a-star-graph :ahss} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "21,200" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:100000]"} {}) #_ "/Users/jawolfe/Desktop/charts/suboptimal-ww-refs.pdf")

  

  
  )

(defn make-online-experiment-set []
  (make-aij-experiment-set "online-test" 1000000
    [:product
     [:max-primitives [nil 5]]
     [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]]
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [100 500]]
;		     [:size     [100]]
		     [:switches [0.001 0.01]] ; 0.10]]
;		     [:switches [0.001]]
		     [:run      [1 2 3]]
;		     [:run      [1]]
		     [:high-level-hla-set ['#{act go}]]
		     [:ref-level-map [nil]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved* `warehouse/*warehouse-hierarchy-nl-improved*]]
		     [:instance-num (vec (range 21))]
;		     [:instance-num [9 16 18]]
;		     [:instance-num [1]]
		     [:high-level-hla-set ['#{act move-blocks}]]
		     [:ref-level-map [nil]]
		    ]]]]
     [:algorithm [:ahlrta-star]]
     [:algorithm-fn [`online/ahlrta-star-search]]
     [:max-steps [10000]]
;     [:max-steps [300]]
     [:max-refs  [10 20 50 100 200 500 1000 2000 5000]]
;     [:max-refs  [10 30 100 300 1000 ]]
;     [:max-refs  [10 ]]
     [:type [] [[:flat-hierarchy
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]
		[:hierarchy 
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
				  [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]]]]
     [:graph?         [:full]]
     [:recheck-graph? [true]]
     ]))

(comment 
  (def *online* (experiment-set-results->dataset (read-experiment-set-results (make-online-experiment-set) "/Users/jawolfe/Desktop/")))

; scouting out ww
(doseq [i (range 22)]  (plot (ds->chart (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives hierarchy ref-choice] (and ms  (= instance-num i) (nil? max-primitives) (= (count (str hierarchy)) 64) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:algorithm :type :ref-choice] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000" :xlabel (str i)} {})))

"[18 17.0 16 15 14* 13 12* 9* 8-6e 4* 2* 1/0e]"
 
;; Average of selected instances
(plot (ds->chart (ds-summarize (ds-derive (ds-fn [output ] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num max-primitives hierarchy ref-choice] (and ms  (#{18 17 15 14 13 12 11 10  4 3 2 9 5} instance-num) (nil? max-primitives) (= (count (str hierarchy)) 64) (= ref-choice :first-gap))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:type :graph? :ref-choice :algorithm :switches :size :max-refs] [[:cost mean (ds-fn [cost] cost)]]) [:algorithm :type :ref-choice] :max-refs :cost { :xrange "[0:5000]" :key "5000, 2000"  :title "Warehouse world - averaged over 13 instances" :xlabel "Allowed refinements per env step" :ylabel "Cost to reach goal"} {} ) "/Users/jawolfe/Desktop/new-charts/online-ww.pdf")


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





















;; old runs

(comment 


(defn make-offline-experiment-set []
  (make-aij-experiment-set "offline-test" 1000
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]] 
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [5 10 50 100 500]]
		     [:switches [1 5 20 0.01 0.03 0.10]]
		     [:run      [1 2 3]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved*]]
		     [:instance-num (vec (range 23))]
		    ]]]]
      [:union  
         [:product 
            [:type      [:strips]]
	    [:algorithm [] [[:a-star-graph [:algorithm-fn [`textbook/a-star-graph-search]]]]]]
         [:product
	    [:type      [:flat-hierarchy]]
            [:graph?    [:bhaskara :full]]
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]
	    [:recheck-graph? [true]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]]]]
	 [:product
	    [:type      [:hierarchy]]
	    [:recheck-graph? [true]]
            [:graph?    [:bhaskara :full]]
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
			     [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]
			    [:ahss         [:algorithm-fn ['offline/ahss-search]]]
			    [:optimistic5  [:product [:algorithm-fn ['offline/optimistic-aha-star-search]]
					             [:algorithm-args [[1.05 `(alts/get-weighted-aha-star-priority-fn 2.0)]]]]]]]]]]))
	 
  ; All algorithms ran out of memory (hard) on problem 16. 
  (let [ww-order [6 0 7 8 1 21 2 5 22 11 3 9 12 4 13 14 15 10 17 18 20 19]] ; 16 
    (def *offline* 
	 (map (fn [m] (if (= :warehouse (:domain m)) 
			(update-in m [:instance-num] #(position % ww-order)) 
			m)) 
	      (experiment-set-results->dataset (read-experiment-set-results (make-offline-experiment-set) "/Users/jawolfe/Desktop/")))))

  (plot (ds->chart (filter (ds-fn [type domain] (and (= type :strips) (= domain :warehouse))) *offline*) [] :instance-num :ref-count {:ylog "t"} {}))
 
  (plot (ds->chart (filter (ds-fn [domain ms] (and ms (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "8,100000" :yrange "[10:100000]"} {}))

(plot (ds->chart (filter (ds-fn [algorithm domain timeout? memout?] (and (not timeout?) (not memout?) (= domain :warehouse) (contains? #{:aha-star :a-star-graph} algorithm))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "22,200" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:100000]"} {}) #_ "/Users/jawolfe/Desktop/charts/optimal-ww-refs.pdf")

(plot (ds->chart (filter (fn [m] (contains? #{nil :full} (:graph? m))) (filter (ds-fn [algorithm domain ms] (and ms (= domain :warehouse) (contains? #{:aha-star :a-star-graph :ahss} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "21,200" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:100000]"} {}) #_ "/Users/jawolfe/Desktop/charts/suboptimal-ww-refs.pdf")

(plot (ds->chart (ds-summarize (filter (fn [m] (and (contains? #{:full nil} (:graph? m)) (contains? #{:first-gap nil} (:ref-choice m)))) (filter (ds-fn [type algorithm domain] (and (= domain :nav-switch) (#{:strips :hierarchy} type) (#{:aha-star :a-star-graph} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm :switches :size] [[:ref-count  (fn [& args] (when (every? first args) (apply mean (map second args)))) (ds-fn [run ref-count] [run ref-count])]])  [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:ylog "t" :xlog "t" :key "45,1000000" :xlabel "Nav size" :ylabel "Number of refs" :xrange "[5:1000]" :yrange "[10:1000000]"} {}) #_"/Users/jawolfe/Desktop/charts/optimal-nav-refs.pdf")  

  
  )


(comment 


(defn make-online-experiment-set []
  (make-aij-experiment-set "online-pretest" 1000000
    [:product
     [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]] 
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [100 500]]
;		     [:size     [100]]
		     [:switches [0.001 0.01]] ; 0.10]]
;		     [:run      [1]]
		     [:run      [1 2 3]]
		     [:high-level-hla-set ['#{act go}]]
		     [:max-primitives [nil 5]]
		     [:ref-level-map [nil '{act 1 go 2 nav 3}]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved*]]
		     [:instance-num [9 16 18]]
		     [:high-level-hla-set ['#{act move-to move-blocks move-block navigate}]]
		     [:max-primitives [nil 5]]
		     [:ref-level-map [nil '{act 0 move-blocks 1 move-to 2 move-block 2 navigate 3 nav 4}]]
		    ]]]]
     [:algorithm [:ahlrta-star]]
     [:algorithm-fn [`online/ahlrta-star-search]]
     [:max-steps [10000]]
;     [:max-steps [300]]
     [:max-refs  [10 20 50 100 200 500 1000 2000 5000]]
;     [:max-refs  [10 30 100 300 1000 ]]
;     [:max-refs  [10 ]]
     [:type [] [[:flat-hierarchy
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]
		[:hierarchy 
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
				  [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]]]]
     [:graph?         [:full]]
     [:recheck-graph? [true]]
     ]))

  (def *online* (experiment-set-results->dataset (read-experiment-set-results (make-online-experiment-set) "/Users/jawolfe/Desktop/")))

  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -20000))) (filter (ds-fn [ms instance-num max-primitives ref-level-map] (and ms (not ref-level-map) (= instance-num 9) (= max-primitives 5))) (filter (ds-fn [domain] (= domain :warehouse)) *online*)) :cost) [:algorithm :type :ref-choice ] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {})) 
 
  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -20000))) (filter (ds-fn [ms size max-primitives ref-level-map] (and ms (not ref-level-map)  (not max-primitives) (= size 500))) (filter (ds-fn [domain] (= domain :nav-switch)) *online*)) :cost) [:algorithm :type :ref-choice ] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {}))

  )

(comment 

(defn make-online-experiment-set2 []
  (make-aij-experiment-set "online-pretest2" 1000000
    [:product
     [:domain [] [[:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved*]]
		     [:instance-num [2 3 5]]
		     [:high-level-hla-set ['#{act move-to move-blocks move-block navigate}
					   '#{act move-blocks}]]
		     [:max-primitives [5]]
		     [:ref-level-map [nil '{act 0 move-blocks 1 move-to 2 move-block 2 navigate 3 nav 4}]]
		    ]]]]
     [:algorithm [:ahlrta-star]]
     [:algorithm-fn [`online/ahlrta-star-search]]
     [:max-steps [10000]]
;     [:max-steps [300]]
     [:max-refs  [10 20 50 100 200 500 1000 2000 5000]]
;     [:max-refs  [10 ]]
     [:type [] [[:flat-hierarchy
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]]]]
		[:hierarchy 
		 [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
				  [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]]]]
     [:union [:product [:graph? [:full]]     [:recheck-graph? [true]]]
             [:product [:graph? [:bhaskara]] [:recheck-graph? [false]]]]
     ]))

    (def *online2* (experiment-set-results->dataset (read-experiment-set-results (make-online-experiment-set2) "/Users/jawolfe/Desktop/")))

  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num ref-level-map] (and ms (not ref-level-map) (= instance-num 3))) (filter (ds-fn [domain] (= domain :warehouse)) *online2*)) :cost) [:algorithm :type :ref-choice :graph?] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {}))
 

  )



(comment 
    (def *online2* (experiment-set-results->dataset (read-experiment-set-results (make-online-experiment-set2) "/Users/jawolfe/Desktop/")))

  (plot (ds->chart (ds-derive (ds-fn [output] (- (or (second output) -10000))) (filter (ds-fn [ms instance-num ref-level-map] (and ms (not ref-level-map) (= instance-num 3))) (filter (ds-fn [domain] (= domain :warehouse)) *online2*)) :cost) [:algorithm :type :ref-choice :graph?] :max-refs :cost {:ylog "t" :xlog "t" :key "7000, 6000"} {}))
 

  )

(comment 
  (def *online* (experiment-set-results->dataset (read-experiment-set-results (make-online-experiment-set) "/Users/jawolfe/Desktop/")))
  )

(comment 
 ; This was for the old run. 
  ; Note: current run forgot to turn on recheck-graph? -- change is minimal for ww, zero for ww.

  (def *ww-diff* [6 7 0 8 1 2 5 9 3 10 4])
  (def *offline* 
       (map (fn [m] (if (= :warehouse (:domain m)) 
		      (update-in m [:instance-num] #(position % *ww-diff*)) 
		      m)) 
     (experiment-set-results->dataset (read-experiment-set-results (make-offline-experiment-set)))))

  (plot (ds->chart (filter (ds-fn [type domain] (and (= type :strips) (= domain :warehouse))) *offline*) [] :instance-num :ref-count {:ylog "t"} {}))

(plot (ds->chart (filter (ds-fn [domain] (and (= domain :warehouse))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "4,100000"} {}))

(plot (ds->chart (filter (ds-fn [algorithm domain timout?] (and (not timout?) (= domain :warehouse) (contains? #{:aha-star :a-star-graph} algorithm))) *offline*) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "4.5,10000" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:10000]"} {}) "/Users/jawolfe/Desktop/charts/optimal-ww-refs.pdf")

(plot (ds->chart (filter (fn [m] (contains? #{nil :full} (:graph? m))) (filter (ds-fn [algorithm domain timout?] (and (not timout?) (= domain :warehouse) (contains? #{:aha-star :a-star-graph :ahss} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm] :instance-num :ref-count {:ylog "t" :key "4.5,10000" :xlabel "WW instance" :ylabel "Number of refs" :yrange "[10:10000]"} {}) "/Users/jawolfe/Desktop/charts/suboptimal-ww-refs.pdf")

(plot (ds->chart (filter (fn [m] (and (contains? #{:full nil} (:graph? m)) (contains? #{:first-gap nil} (:ref-choice m)))) (filter (ds-fn [type algorithm domain timout?] (and (not timout?) (= domain :nav-switch) (#{:strips :hierarchy} type) (#{:aha-star :a-star-graph} algorithm))) *offline*)) [:type :graph? :ref-choice :algorithm :switches] :size :ref-count {:ylog "t" :xlog "t" :key "30,10000" :xlabel "Nav size" :ylabel "Number of refs" :xrange "[5:500]" :yrange "[10:10000]"} {}) "/Users/jawolfe/Desktop/charts/optimal-nav-refs.pdf")



 )

; (let [e (constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))] (doseq [[n h] [["flat" (get-flat-strips-hierarchy e [:warehouse-act])] ["hierarchcial" (get-hierarchy *warehouse-hierarchy-improved* e)]]] (println n (get-time-pair (do (reset-ref-counter) [(second (aha-star-search (alt-node h {:graph? :full :recheck-graph? true}))) (sref-get *ref-counter*)])))))

;(dotimes [i 6] (println "\n\n" i) (let [e (nth *icaps-ww* i)] (doseq [[n h] [["flat-heuristic        " (get-flat-strips-hierarchy e [:warehouse-act])] ["flat-unguided         " (get-flat-strips-hierarchy e)] ["hierarchical-heuristic" (get-hierarchy *warehouse-hierarchy-improved* e)] ["hierarchical-unguided " (get-hierarchy *warehouse-hierarchy-unguided* e)]]] (println n (get-time-pair (do (reset-ref-counter) [(second (aha-star-search (alt-node h {:graph? :full :recheck-graph? true}))) (sref-get *ref-counter*) (sref-get *plan-counter*)]))))))


; (plot (ds->chart (ds-summarize (experiment-set-results->dataset (read-experiment-set-results (make-nav-switch-experiment-set))) [:type :size :switches] [[:ms (fn [& args] (when (every? identity args ) (apply mean args))) (ds-fn [ms] ms)]]) [:type :switches] :size :ms {:key "top left" :xlabel "size" :ylabel "ms" :title "square nav-switch solution time, grouped by n-switches" :ylog true :xlog true :xtics "4, 2, 256"} (fn [[type switches]] {:lt ({0 1 1 2 20 3} switches) :lc ({:hierarchy (gp-rgb 255 0 0) :flat-hierarchy (gp-rgb 0 255 0) :strips (gp-rgb 0 0 255)} type)})))

(defn compare-nav-switch-flat-es []
  (make-aij-experiment-set "compare-nav-switch-flat" 30
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [(fn [m] `(nav-switch/make-flat-nav-switch-heuristic [0 ~(dec (:size m))]))]] 
		     [:size     [5 10 20 50]]
		     [:switches [0 5]]
		     [:run      [1]]]]]]
     [:algorithm [`offline/aha-star-search]]
      [:type   [] [[:hierarchy       [:hierarchy [`nav-switch/*nav-switch-hierarchy*
						  `nav-switch/*nav-switch-flat-hierarchy*]]]
		   [:flat-hierarchy  [:hierarchy ['none]]]]]]))

;(plot (ds->chart (experiment-set-results->dataset *r*) [:hierarchy :switches] :size :ms))




;Variables:
;  - Algorithm
;    - Algorithm parameters
;     - Priority fn
;     - Threshold
;     - Max refinements (online)
;    - ALT parameters
;     - Graph type
;     - Caching
;     - Ref choice fn
;  - Domain :result-
;    - Hierarchy / Heuristic / subsumption
;    - Problem Instance
;  - Formulation (Strips/Strips-hierarchy/Hierarchy)
;
;Hierarchical Algorithms:
; - HFS    
; - AHA*
; - AHSS (threshold, priority fn)
; - WAHA* (weight)
; - OAHA* (weight, priority fn)
0; - AHLRTA*  (max-refs, HLAs)
; - IAHLRTA* (max-refs)
;
; * Decomposition (briefly mention, at least) 
; * Early return (first primitive action)?
; 
;Abstract Lookahead Trees
; - Ref choice fn (s)
; - Caching (?)
; - Graph types (off, old, new, full ?)
;
;Domains 
; - Warehouse (w/wo heuristic)?
; - Nav-switch (w/better pess) 
; - DRT        (types)
; 
;
;Flat:
; - Just briefly report on speed gap
;
;


;experiments
; - Offline
;    - Incl. various offline and online 
;    - Grounded STRIPS (+heuristic)
;    - Flat-strips hierarchy (+heuristic)
;    - Real hierarchy (pick1)
; - Online;

;Missing things in experiments
; - Support for old graph (done)
; - Support for singleton-only graph (?)

; Weighted ICAPS fn.

; Guided and unguided hierarchies.




(comment 

(use 'edu.berkeley.ai.util.datasets 'edu.berkeley.ai.util.charts 'edu.berkeley.ai.scripts.experiments 'edu.berkeley.ai.scripts.z09-aij :reload-all)

(plot (ds->chart (experiment-set-results->dataset (run-experiment-set (make-09-aij-offline-experiment-set))) [:algorithm :domain] :max-mb :ms))



; AHA* with various versions of nav switch
(def *results*
(doall (run-experiment-set
(make-experiment-set "nav-switch-aha-star"
  (parameter-set-tuples '[:product [:size [5 10 20]] [:switches [0 1 5 20]] [:run [1 2 3 4 5 6 7 8 9 10]]]
    (fn [m] `(alt-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-random-nav-switch-strips-env ~(:size m) ~(:switches m))))))
    (fn [m] `(solution-name (aha-star-search ~'init))))
  'user nil 20 512 nil *planning-experiment-result*))))

(plot (ds->chart (ds-summarize (experiment-set-results->dataset *results*) [:size :switches] [[:ms mean (ds-fn [ms] ms)]]) [:switches] :size :ms))

(plot (ds->chart (ds-derive (ds-fn [output] (- (second output))) (filter (ds-fn [run] (= run 1)) (experiment-set-results->dataset *results*)) :cost) [:switches] :size :cost))

; Compare speed of two flat strips hierarchies.  Flat2 is slightly faster.
(def *args* (map-map #(vector % (make-random-nav-switch-args % 3)) [5 10 20 50]))
(def *results*
(doall (run-experiment-set
(make-experiment-set "nav-switch-hierarchy-vs-flats"
  (parameter-set-tuples '[:product [:size [5 10 20 50]] [:type [:hierarchical :flat1 :flat2]]]
    (fn [m] 
      (cond (= (:type m) :hierarchical)
	      `(alt-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get *args* (:size m))))))
	      (= (:type m) :flat1)
	      `(alt-node (get-hierarchy *nav-switch-flat-hierarchy* (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get *args* (:size m))))))
	      (= (:type m) :flat2)
	      `(alt-node (get-flat-strips-hierarchy (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get *args* (:size m)))) (make-flat-nav-switch-heuristic [0 ~(dec (:size m))])))
	      :else (throw (Exception.))))
    (fn [m] `(solution-name (aha-star-search ~'init))))
  'user nil 20 512 nil *planning-experiment-result*))))

(plot (ds->chart (experiment-set-results->dataset *results*) [:type] :size :ms))


; Simple Nav-switch AHA* results
(def get-ns-args (memfn (fn [size switches run] (make-random-nav-switch-args size switches))))

(def *results2*
(doall (run-experiment-set
(make-experiment-set "nav-switch-aha-star"
  (parameter-set-tuples '[:product 
			  [:size [5 20 50 200]] 
			  [:switches [0 1 20]] 
			  [:run [1 2 3]]
			  [:type [:hierarchy :flat-hierarchy :strips]]
			  ]
    (fn [m] 
      (cond (= (:type m) :hierarchy)
	      `(alt-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get-ns-args (:size m) (:switches m) (:run m))))))
	      (= (:type m) :flat-hierarchy)
	      `(alt-node (get-flat-strips-hierarchy (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get-ns-args (:size m) (:switches m) (:run m)))) (make-flat-nav-switch-heuristic [0 ~(dec (:size m))])))
	      (= (:type m) :strips)
	      `(ss-node (constant-predicate-simplify (apply make-nav-switch-strips-env '~(get-ns-args (:size m) (:switches m) (:run m)))) (make-flat-nav-switch-heuristic [0 ~(dec (:size m))]))
	      :else (throw (Exception.))))
    (fn [m] 
      (cond (= (:type m) :strips)
	      `(solution-name (a-star-graph-search ~'init))
	    :else
	      `(solution-name (aha-star-search ~'init)))))
  'user nil 20 512 nil *planning-experiment-result*))))

(plot (ds->chart (ds-summarize (experiment-set-results->dataset *results2*) [:type :size :switches] [[:ms (fn [& args] (when (every? identity args ) (apply mean args))) (ds-fn [ms] ms)]]) [:type :switches] :size :ms {:key "top left" :xlabel "size" :ylabel "ms" :title "square nav-switch solution time, grouped by n-switches" :ylog true :xlog true :xtics "4, 2, 256"} (fn [[type switches]] {:lt ({0 1 1 2 20 3} switches) :lc ({:hierarchy (gp-rgb 255 0 0) :flat-hierarchy (gp-rgb 0 255 0) :strips (gp-rgb 0 0 255)} type)})))

)

