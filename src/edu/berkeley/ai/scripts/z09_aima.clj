(ns edu.berkeley.ai.scripts.z09-aima
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
	   [edu.berkeley.ai.util [charts :as charts] [datasets :as datasets]]
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains [strips :as strips] [vac-rooms :as vac-rooms]]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-valuations :as dv]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies [strips-hierarchies :as strips-hierarchies] 
	    [abstract-lookahead-trees :as alts] [offline-algorithms :as offline]
	    [online-algorithms :as online]]
	   [edu.berkeley.ai.scripts.experiments :as experiments]
	   )
 )

(def *vac-args*
     [[4 4 [[[0 0] [1 1]]] 
       [] 
       [0 0]]
      [4 4 [[[0 0] [1 1]] [[2 0] [3 1]]] 
       [[[1 0] [2 0]] [[1 1] [2 1]]] 
       [0 0]]
      [4 4 [[[0 0] [1 1]] [[2 0] [3 1]] [[0 2] [1 3]]] 
       [[[1 0] [2 0]] [[0 1] [0 2]] [[1 2] [2 1]]] 
       [0 0]]
      [4 4 [[[0 0] [1 1]] [[2 0] [3 1]] [[0 2] [1 3]] [[2 2] [3 3]]] 
       [[[1 0] [2 0]] [[0 1] [0 2]] [[1 3] [2 3]] [[3 1] [3 2]]] 
       [0 0]]])

(def *rlm* {'act 10 'finish-cleaning 9 'clean-room 8 'clean-rows 7 'clean-row 6 'nav-left 5 'nav 4})
; (first (hla-name (first h))) 11

(defn get-vac-env-init-form [m]
  `(strips/constant-predicate-simplify
    (apply vac-rooms/make-vac-rooms-strips-env '~(nth *vac-args* (:instance-num m)))))

(defn get-vac-hierarchy-init-form [m env-form]
  (condp = (:type m)
    :hierarchy       `(hierarchies/get-hierarchy vac-rooms/*vac-rooms-hierarchy* ~env-form)
    :strips          env-form))


(defn get-vac-node-init-form [m hierarchy-form]
  (condp = (:type m)
         :strips
	  `(search/ss-node ~hierarchy-form)
         :hierarchy
	    `(alts/alt-node ~hierarchy-form		
		{:graph? false  :recheck-graph? false :cache? false
		 :ref-choice-fn ~(condp = (:ref-choice m) 
				   :first `alts/first-choice-fn  
				   :first-highest `(alts/make-first-maximal-choice-fn *rlm*))})))

(defn get-vac-init-form [m]
  (get-vac-node-init-form m (get-vac-hierarchy-init-form m (get-vac-env-init-form m))))

(defn get-vac-solution-form [m]
  `(envs/solution-name 
    (~(condp = (:algorithm m)
	:bfs `offline/new-hierarchical-forward-search
	:dfs `offline/new-hierarchical-forward-search-id
	:idfs `offline/new-hierarchical-forward-search-id)
     ~'init
     ~(:prune m)
     ~(when (:commit m) `*rlm*)
     ~@(when (= (:algorithm m) :dfs) ['[Double/POSITIVE_INFINITY]]))))

(defn make-aima-experiment-set [name max-seconds arg-spec]
  (experiments/make-experiment-set name
    arg-spec get-vac-init-form get-vac-solution-form
    'edu.berkeley.ai.scripts.z09-aima 10
     max-seconds 512 false experiments/*planning-experiment-result*))


(defn make-vac-experiment-set []
  (make-aima-experiment-set "vac" 3600
    [:product
      [:instance-num (vec (range 4))]
      [:algorithm [:bfs :dfs :idfs]]
      [:union  
       [:type      [:strips]]
       [:product 
	 [:type       [:hierarchy]]
	 [:ref-choice [:first :first-highest]]
	 [:prune      [true false]]
	 [:commit     [true false]]]]]))

; (Randomized) DFS.

(defonce *vac* nil)

(defn read-vac-results []
  (def *vac* 
       (experiments/experiment-set-results->dataset
	(experiments/read-experiment-set-results (make-vac-experiment-set)))))

(defn make-vac-csv []
  (util/spit "/Users/jawolfe/Desktop/vac.csv"
    (util/str-join "\n"
      (map #(util/str-join "," %)
	(cons ["rooms" "type" "search-strategy" "prune" "commit" "choice" 
	       "timeout?" "memout?" "plans" "refs" "ms"]
	  (for [{:keys [instance-num algorithm type ref-choice prune commit 
			timeout? memout? plan-count ref-count ms]} *vac*]
	    (concat [(inc instance-num) type algorithm]
		    (if (= type :strips) ["", "", ""] [prune commit ref-choice])
		    [timeout? memout?]
		    (when-not (or timeout? memout?)
		      [plan-count ref-count ms]))))))))
	     

(comment
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
      {:term "solid color size 3,2"
       :ylog "t" :key "12,100000" :yrange "[10:200000]" :xlabel "Problem Number" :ylabel y-label
       :title "Offline Warehouse World" } 
      (constantly {:lw 4})
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
      {:term "solid color size 3,2"
       :ylog "t" :xlog "t" :key "45,100000"
       :title "Offline Nav Switch"
       :xlabel "Board size (per side)" :ylabel y-label 
       :xrange "[5:1000]" :yrange "[50:200000]"} 
      (constantly {:lw 4})
      (fn [[type graph ref-choice alg]]
	(cond (= alg :ahss) "AHSS" (= type :hierarchy) "AHA*" :else "Graph A*"))
      identity)
     (str dir "offline-nav-" file-suffix ".pdf")))      
   ))

     )


