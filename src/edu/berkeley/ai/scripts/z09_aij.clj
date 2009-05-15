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
      [4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]]
      [7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]]]])

(def get-ns-args (memoize (fn [size switches run] (nav-switch/make-random-nav-switch-args size switches))))

(defn get-ns-form [size switches run]
  `(strips/constant-predicate-simplify 
    (apply nav-switch/make-nav-switch-strips-env 
	   '~(get-ns-args size switches run))))

(defn get-warehouse-form [args]
  `(strips/constant-predicate-simplify
    (apply warehouse/make-warehouse-strips-env '~args)))

(defn get-env-init-form [m]
  (condp = (:domain m)
    :nav-switch (get-ns-form (:size m) (:switches m) (:run m))
    :warehouse  (get-warehouse-form (nth *warehouse-args* (:instance-num m)))))

(defn get-hierarchy-init-form [m env-form]
  (condp = (:type m)
    :hierarchy       `(hierarchies/get-hierarchy ~(:hierarchy m) ~env-form)
    :flat-hierarchy  `(let [env# ~env-form] (strips-hierarchies/get-flat-strips-hierarchy env# (~(:heuristic m) env#)))
    :strips          env-form))

(defn get-node-init-form [m hierarchy-form]
  (cond (contains? #{:hierarchy :flat-hierarchy} (:type m))
	  `(alts/alt-node ~hierarchy-form ~{:graph? (:graph? m) :ref-choice-fn (:choice-fn m)}) ;TODO
	(= :strips (:type m))
	  `(let [env# ~hierarchy-form] (search/ss-node env# (~(:heuristic m) env#)))))

(defn get-init-form [m]
  (get-node-init-form m (get-hierarchy-init-form m (get-env-init-form m))))

(defn get-solution-form [m]
  `(envs/solution-name (~(:algorithm-fn m) ~'init ~@(:algorithm-args m))))

(defn make-aij-experiment-set [name max-seconds arg-spec]
  (experiments/make-experiment-set name
    arg-spec get-init-form get-solution-form
    'edu.berkeley.ai.scripts.z09-aij nil ;10
     max-seconds 512 nil experiments/*planning-experiment-result*))



(defn make-offline-experiment-set []
  (make-aij-experiment-set "nav-switch-test" 1
    [:product
      [:domain [] [[:nav-switch 
		    [:product
		     [:heuristic [`nav-switch/make-flat-nav-switch-heuristic]] 
		     [:hierarchy [`nav-switch/*nav-switch-hierarchy*]]
		     [:size     [5 10 50 100 500]]
		     [:switches [1 3 10]]
		     ;[:run      [1]]
		     ]]
		   [:warehouse
		    [:product
		     [:heuristic [`warehouse/make-flat-warehouse-heuristic]] 
		     [:hierarchy [`warehouse/*warehouse-hierarchy-improved*]]
		     [:instance-num [0 1 2 3 4 5 6 7 8 9 10]]
		    ]]]]
      [:union  
         [:product 
            [:type      [:strips]]
	    [:algorithm [] [[:a-star-graph [:algorithm-fn [`textbook/a-star-graph-search]]]]]]
         [:product
	    [:type      [:flat-hierarchy]]
            [:graph?    [:bhaskara :full]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]]]]
	 [:product
	    [:type      [:hierarchy]]
            [:graph?    [:bhaskara :full]]
	    [:ref-choice [] [[:first-gap [:choice-fn [`alts/first-gap-choice-fn]]]
			     [:icaps     [:choice-fn [`alts/icaps-choice-fn]]]]]
	    [:algorithm [] [[:aha-star     [:algorithm-fn ['offline/aha-star-search]]]
			    [:ahss         [:algorithm-fn ['offline/ahss-search]]]
			    [:optimistic5  [:product [:algorithm-fn ['offline/optimistic-aha-star-search]]
					             [:algorithm-args [[1.05 `(alts/get-weighted-aha-star-priority-fn 2.0)]]]]]]]]]]))
	    



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

