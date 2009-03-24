(ns edu.berkeley.ai.domains.09-aij
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains [strips :as strips] [nav-switch :as nav-switch] [warehouse :as warehouse]]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-simple-valuations :as dnf-simple-valuations]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies [strips-hierarchies :as strips-hierarchies] 
	    [abstract-lookahead-trees :as alts] [offline-algorithms :as offline]
	    [online-algorithms :as online]]
	   )
 )

;experiments
; - Offline
;    - Incl. various offline and online 
;    - Grounded STRIPS (+heuristic)
;    - Flat-strips hierarchy (+heuristic)
;    - Real hierarchy (pick1)
; - Online;
;
; - Things to measure
;   - time
;   - memory (?)
;   - number of refinements/expansions
;   - number of next-states/progressions 
;
;- Cluster framework?
;  - Given set of jobs, (cartesian product?), folder location, number,
;  - ... do this job
;   - Clojure launcher for cluster run would be nice
;   - One potential hitch: dependencies between jobs
;      - May have lattice, if one job times out, don't bother with more
;         difficult jobs.  Only within runs on a single machine?  Then,
;         need way to specify granularity of batching, ...
;




(def *tiny-ww* ["tiny 2x2" -4 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))])

(def *small-ww* ["small 3x3" -7 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]]))])

(def *med-ww* ["med 3x4" -14 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))])

(def *long-ww* ["long 4x4" -50 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))])

(def *big-ww* ["big 7x6" -50 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]]))])

(def *all-ww* [*tiny-ww* *small-ww* *med-ww* *long-ww* *big-ww*])

(def *search-fns* [["a-star" textbook/a-star-search] ["a-star graph" textbook/a-star-graph-search]])

(def *node-fns* [;["strips" search/ss-node] 
		 ;["flat-strips" #(hierarchies/alt-node (strips-hierarchies/get-flat-strips-hierarchy %))]
		 ;["unguided" #(hierarchies/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %))]
;		 ["unguided-alt-ff" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) false false)]
;		 ["unguided-alt-tf" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) true false)]
;		 ["unguided-alt-ft" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) false true)]
;		 ["unguided-alt-tt" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %) true true)]
		 ["guided-alt-tp" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy* %) true true)]
;		 ["guided-alt-tt" #(alts/alt-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy* %) true :full)]
		 ])


(def *time-limit* 30)

(defn- pad [thing len]
  (.substring (apply str thing (replicate len " ")) 0 len))
(defn- print-pad [len & args]
  (print (pad (apply str (next (interleave (repeat " ") args))) len)))


(defn- time-ww 
  ([env-v search-fn-v nf-v] (time-ww env-v search-fn-v nf-v true))
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
	  env-v    *all-ww*
	  search-v (butlast *search-fns*)]
    (time-ww env-v search-v node-v))

  (doseq [node-v *node-fns*   ; Check for heuristic inconsistencies... looks OK.
	  env-v  *all-ww*]
    (time-ww env-v ["ahss" #(algs/ahss-search % (second env-v))] node-v))

  (doseq [node-v *node-fns*   
	  env-v  *all-ww*]
    (time-ww env-v ["ahss" #(let [r (algs/ahss-search %)] (println (second r)) r)] node-v false))
  )



; (interactive-search (tdf-node (get-hierarchy *warehouse-hierarchy-unguided* (constant-predicate-simplify (make-warehouse-strips-env 7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]])))) (make-tree-search-pq) #(- (upper-reward-bound %)))
