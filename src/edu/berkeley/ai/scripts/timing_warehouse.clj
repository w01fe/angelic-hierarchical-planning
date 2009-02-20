(ns edu.berkeley.ai.domains.timing-warehouse
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips]
	   [edu.berkeley.ai.domains.warehouse :as warehouse]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-simple-valuations :as dnf-simple-valuations]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as strips-hierarchies]
	   )
 )

; instance-info
; hierarchy-schema
; graph?

(def *tiny-ww* ["tiny 2x2" -4 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 2 2 [1 1] false {0 '[a]} nil ['[a table1]]))])

(def *small-ww* ["small 3x3" -7 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 3 3 [1 1] false {0 '[a] 2 '[b]} nil ['[b a]]))])

(def *med-ww* ["med 3x4" -14 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))])

(def *long-ww* ["long 4x4" -50 (strips/constant-predicate-simplify (make-warehouse-strips-env 4 4 [1 2] false {0 '[a] 2 '[c b]} nil ['[a c table1]]))])

(def *big-ww* ["big 7x6" -50 (strips/constant-predicate-simplify (warehouse/make-warehouse-strips-env 7 6 [0 2] true {0 '[b] 1 '[a] 2 '[c]  } nil ['[a b c table5]]))])

(def *all-ww* [*tiny-ww* *small-ww* *med-ww* *long-ww* *big-ww*])

(def *search-fns* [["a-star" textbook/a-star-search] ["a-star graph" textbook/a-star-graph-search]])

(def *node-fns* [;["strips" search/ss-node] 
		 ["flat-strips" #(hierarchies/tdf-node (strips-hierarchies/get-flat-strips-hierarchy %))]
		 ["unguided-hierarchy" #(hierarchies/tdf-node (hierarchies/get-hierarchy warehouse/*warehouse-hierarchy-unguided* %))]])

(def *time-limit* 10)

(defn- pad [thing len]
  (.substring (apply str thing (replicate len " ")) 0 len))
(defn- print-pad [len & args]
  (print (pad (apply str (rest (interleave (repeat " ") args))) len)))


(defn- time-ww [env-v search-fn-v nf-v]
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
	      (util/assert-is (= env-rew (second ret)))      
	      (print-pad 10 nt)
	      (print " + ")
	      (print-pad 10 st)
	      (println " = " (+ nt st)))))))))
  
(comment
  (doseq [node-v   *node-fns*
	  env-v    *all-ww*
	  search-v (butlast *search-fns*)]
    (time-ww env-v search-v node-v))
  )