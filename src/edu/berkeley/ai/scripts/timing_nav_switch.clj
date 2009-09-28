(ns edu.berkeley.ai.scripts.timing-nav-switch
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.envs.strips :as strips]
	   [edu.berkeley.ai.domains.nav-switch :as nav-switch]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-valuations :as dnf-valuations]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as strips-hierarchies]
	   [edu.berkeley.ai.angelic.algorithms
	                                        [abstract-lookahead-trees :as alts]
	                                        [offline-algorithms :as algs]]
	   )
 )





(def *small-ns* ["small 5x5x1" -21 (strips/constant-predicate-simplify (nav-switch/make-nav-switch-strips-env 5 5 [[1 1]] [0 4] false [4 0]))])

(def *med-ns*   ["med 20x20x3" -92 (strips/constant-predicate-simplify (nav-switch/make-nav-switch-strips-env 20 20 [[3 7] [12 18] [16 2]] [19 0] true [0 19]))])

(def *big-ns*   ["big 100x100x10" -433 (strips/constant-predicate-simplify (nav-switch/make-nav-switch-strips-env 100 100 [[26 91] [50 24] [54 97] [2 35] [25 9] [34 53] [2 16] [49 47] [67 10] [23 82]] [99 0] true [0 99]))])

; (vec (take 10 (repeatedly (fn [] [(rand-int 100) (rand-int 100)]))))


(def *all-ns* [*small-ns* *med-ns* *big-ns*])

(util/defvar- *search-fns* [["aha-star" algs/aha-star-search true] ["ahss-search" algs/ahss-search false]])

(util/defvar- *node-fns* [;["strips" search/ss-node] 
		 ;["flat-strips" #(hierarchies/alt-node (strips-hierarchies/get-flat-strips-hierarchy %))]
		 ;["unguided" #(hierarchies/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %))]
;		 ["unguided-alt-ff" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) false false)]
;		 ["unguided-alt-tf" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) true false)]
;		 ["unguided-alt-ft" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) false true)]
;		 ["unguided-alt-tt" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) true true)]
		 ["guided-alt-tp" #(alts/alt-node (hierarchies/get-hierarchy nav-switch/*nav-switch-hierarchy* %) {:cache? true :graph? true})]
		 ["guided-alt-tt" #(alts/alt-node (hierarchies/get-hierarchy nav-switch/*nav-switch-hierarchy* %) {:cache? true :graph? :full})]
		 ])

(util/defvar- *time-limit* 20)

(defn- pad [thing len]
  (.substring (apply str thing (replicate len " ")) 0 len))
(defn- print-pad [len & args]
  (print (pad (apply str (next (interleave (repeat " ") args))) len)))

(defn- time-ns 
  ([env-v search-fn-v nf-v] (time-ns env-v search-fn-v nf-v true))
  ([env-v search-fn-v nf-v strict?]
;;  (println)
  (let [[env-name env-rew env] env-v
	[sf-name sf] search-fn-v
	[nf-name nf] nf-v]
    (print-pad 50 "Timing" nf-name env-name sf-name ": ")
    (flush)
    (let [nv (util/time-limit (nf env) *time-limit*)]
      (if (= nv :timeout) (println "timeout1")
	(let [[node nt] nv
	      nt (/ (int nt) 1000.0)
	      sv   (util/time-limit (sf node) (- *time-limit* nt))]
;;	  (println node)
	  (if (= sv :timeout) (println nt "+ timeout2")
	    (let [[ret st] sv
		  st (/ (int st) 1000.0)]
;	      (println sv)
	      (if strict? (util/assert-is (= env-rew (second ret)))      
		  (util/assert-is (and (second ret) (>= env-rew (second ret)))))
	      (print-pad 10 nt)
	      (print " + ")
	      (print-pad 10 st)
	      (println " = " (+ nt st))))))))))
  
(comment
  (doseq [node-v   *node-fns*
	  env-v    *all-ns*
	  search-v *search-fns*]
    (time-ns env-v search-v node-v (nth search-v 2)))

  (doseq [node-v *node-fns*   ; Check for heuristic inconsistencies... looks OK.
	  env-v  *all-ww*]
    (time-ww env-v ["ahss" #(algs/ahss-search % (second env-v))] node-v))

  (doseq [node-v *node-fns*   
	  env-v  *all-ww*]
    (time-ww env-v ["ahss" #(let [r (algs/ahss-search %)] (println (second r)) r)] node-v false))
  )




(def *nav* 
 (map #(strips/constant-predicate-simplify (apply nav-switch/make-nav-switch-strips-env %))
      [[5 5 [[1 1]] [0 4] false [4 0]]
       [20 20 [[3 7] [12 18] [16 2]] [19 0] true [0 19]]
       [40 40 [[3 7] [12 18] [16 2] [23 16] [11 34] [35 29] [7 11] [28 5] [9 32]] [39 0] true [0 39]]
  ;     [40 40 [[3 7] [12 18] [16 2] [38 1] [38 2] [37 1] [23 16] [11 34] [35 29] [7 11] [28 5] [9 32]] [39 0] true [0 39]]
       [100 100 [[26 91] [50 24] [54 97] [2 35] [25 9] [34 53] [2 16] [49 47] [67 10] [23 82]] [99 0] true [0 99]]]))

(defn test-icaps-nav [i alt-args]
  (let [e (nth *nav* i)
	h (nav-switch/make-flat-nav-switch-heuristic e)] 
    (doseq [[alg node]
	    [[textbook/a-star-graph-search (search/ss-node e h)]
	     [algs/aha-star-search (alts/alt-node (strips-hierarchies/get-flat-strips-hierarchy e h) alt-args)]
	     [algs/aha-star-search (alts/alt-node (hierarchies/get-hierarchy nav-switch/*nav-switch-flat-hierarchy*  e) alt-args)]
	     [algs/aha-star-search (alts/alt-node (hierarchies/get-hierarchy nav-switch/*nav-switch-hierarchy* e) alt-args)]]]
      (search/reset-ref-counter)
      (println [(time (second (alg node))) (util/sref-get search/*ref-counter*)]))))









(comment ; Old versions...

(def *huge-ns-size* 25)
(def *huge-ns-args* [25 25 [[1 1]] [24 0] true [0 24]])
(def *huge-ns-reward* -101)
(def *big-ns-args* [6 6 [[1 1]] [5 0] true [0 5]])
(def *big-ns-reward* -25)
(def *small-ns-args* [5 5 [[1 1]] [0 4] false [4 0]])
(def *small-ns-reward* -21)

(def *search-fn* textbook/a-star-search)

; Right now, using graph search -- huge difference!

(defn- time-and-check-flat 
  ([str rew env] (time-and-check-flat str rew env (constantly 0)))
  ([str rew env heur]
  (println str)
  (util/assert-is 
   (= rew
    (second
     (envs/check-solution env
      (time
       (*search-fn*
	(search/make-initial-state-space-node env heur)))))))))

(def *strips-simplifiers*
     {"unsimplified" identity,
      "constant simplified" strips/constant-predicate-simplify
      "constant simplified, flat" (comp strips/flatten-strips-instance
					strips/constant-predicate-simplify)})

(defn- time-and-check-hierarchical [str reward hierarchy-schema env val-type]
  (println str)
  (let [initial-hla (hierarchies/instantiate-hierarchy hierarchy-schema env)
	node (edu.berkeley.ai.angelic.algorithms.abstract-lookahead-trees/make-initial-alt-node initial-hla {:valuation-type val-type :cache? false :graph? false})]
  (util/assert-is 
   (= reward (second (envs/check-solution (hierarchies/hla-environment initial-hla)
     (time 
      (*search-fn* node
       ))))))))

(def *strips-hierarchy-simplifiers*
     (dissoc *strips-simplifiers* "constant simplified, flat"))

)
(comment
     
(time-and-check-flat 
 "6x6 flat nav-switch (non-strips): " *big-ns-reward*
 (apply nav-switch/make-nav-switch-env *big-ns-args*))

(doseq [[name simplifier] (drop 2 *strips-simplifiers*)]
  (time-and-check-flat
   (format  "6x6 flat nav-switch (strips, %s): " name) *big-ns-reward*
   (simplifier (apply nav-switch/make-nav-switch-strips-env *big-ns-args*))))

(time-and-check-flat 
 "5x5 flat nav-switch (non-strips): " *small-ns-reward*
 (apply nav-switch/make-nav-switch-env *small-ns-args*))


(time-and-check-hierarchical "5x5 flat-hierarchy, non-strips, 0 heuristic" *small-ns-reward*
  (hierarchies/make-flat-hierarchy-schema (constantly 0))
  (apply nav-switch/make-nav-switch-env *small-ns-args*)
  ::angelic/ExplicitValuation)
  
(doseq [[name simplifier] *strips-simplifiers*]
  (time-and-check-hierarchical (format  "5x5 flat-hierarchy, strips, %s, 0 heuristic" name) 
    *small-ns-reward*
    (hierarchies/make-flat-hierarchy-schema (constantly 0))    
    (simplifier  (apply nav-switch/make-nav-switch-strips-env *small-ns-args*))
    ::angelic/ExplicitValuation))

(doseq [[name simplifier] *strips-hierarchy-simplifiers*]
  (time-and-check-hierarchical (format  "5x5 flat-strips-hierarchy, %s, 0 heuristic" name) 
    *small-ns-reward*
    (strips-hierarchies/make-flat-strips-hierarchy-schema 
     (nav-switch/make-nav-switch-strips-domain) (constantly 0))    
    (simplifier (apply nav-switch/make-nav-switch-strips-env *small-ns-args*))
    ::dnf-valuations/DNFValuation))

(doseq [[name simplifier] *strips-hierarchy-simplifiers*]
  (time-and-check-hierarchical (format  "6x6 flat-strips-hierarchy, %s, 0 heuristic" name) 
    *big-ns-reward*
    (strips-hierarchies/make-flat-strips-hierarchy-schema 
     (nav-switch/make-nav-switch-strips-domain) (constantly 0))    
    (simplifier (apply nav-switch/make-nav-switch-strips-env *big-ns-args*))
    ::dnf-valuations/DNFValuation ))

  )
;;;; On to heuristics.

(comment
(time-and-check-flat 
 (str "square " *huge-ns-size* " flat nav-switch (non-strips), heuristic: ") *huge-ns-reward*
 (apply nav-switch/make-nav-switch-env *huge-ns-args*)
 (fn [state] (* -2 (+ (Math/abs (- (first (:pos state)) 0)) (Math/abs (- (second (:pos state)) (dec *huge-ns-size*)))))))

(doseq [[name simplifier] (butlast *strips-simplifiers*)]
  (time-and-check-flat
   (format  "square %s flat nav-switch (strips, %s), heuristic" *huge-ns-size* name) *huge-ns-reward*
   (simplifier (apply nav-switch/make-nav-switch-strips-env *huge-ns-args*))
   (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) (dec *huge-ns-size*))))))))

;; Graph doesn't work with this, so will never finish
(doseq [[name simplifier] *strips-hierarchy-simplifiers*]
  (time-and-check-hierarchical (format  "square %s flat-strips-hierarchy, %s, heuristic" *huge-ns-size* name) 
    *huge-ns-reward*
    (strips-hierarchies/make-flat-strips-hierarchy-schema 
     (nav-switch/make-nav-switch-strips-domain) 
     (fn [state] (* -2 (+ (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'atx)) 1) 0)) (Math/abs (- (util/desymbolize (first (strips/get-strips-state-pred-val state 'aty)) 1) (dec *huge-ns-size*))))))
     )    
    (simplifier (apply nav-switch/make-nav-switch-strips-env *huge-ns-args*))
    ::dnf-valuations/DNFValuation))


(doseq [[name simplifier]  (take 3 *strips-hierarchy-simplifiers*)]
  (time-and-check-hierarchical (format  "square %s strips-hierarchy, %s, heuristic" *huge-ns-size* name) 
    *huge-ns-reward*
    (hierarchies/parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch2.hierarchy" 
     (nav-switch/make-nav-switch-strips-domain)) 
    (simplifier (apply nav-switch/make-nav-switch-strips-env *huge-ns-args*))
    ::dnf-valuations/DNFValuation))
 )

; (let [node (alt-node (get-hierarchy *nav-switch-hierarchy* (constant-predicate-simplify (make-nav-switch-strips-env 505 505 (prln (take 100 (repeatedly #(vector (rand-int 505) (rand-int 505))))) [504 0] true [0 504]))))] (time (filter #(= "flip" (.substring (name (first %)) 0 4)) (map :name (first (a-star-search node))))))