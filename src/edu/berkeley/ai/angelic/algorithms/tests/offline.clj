(ns edu.berkeley.ai.angelic.algorithms.tests.offline
  (:use clojure.test edu.berkeley.ai.angelic.hierarchies
	edu.berkeley.ai.angelic.algorithms.offline)
  (:require [edu.berkeley.ai [util :as util] [search :as search] [envs :as envs]]
	    [edu.berkeley.ai.util.queues :as queues]
		[edu.berkeley.ai.envs.strips :as strips]	
	    [edu.berkeley.ai.domains [nav-switch :as nav-switch] [warehouse :as warehouse]]
	    [edu.berkeley.ai.angelic.algorithms.abstract-lookahead-trees :as alts]
	    )
  )
  


(def *ns-inst* ["ns" -27 nav-switch/*nav-switch-hierarchy* 
		(strips/constant-predicate-simplify
		 (nav-switch/make-nav-switch-strips-env 6 6 [[4 0] [3 3] [0 4]] [5 0] true [0 5]))])

(def *wh-inst* ["wh" -6 warehouse/*warehouse-hierarchy*
		 (strips/constant-predicate-simplify 
		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[c] 3 '[d]} nil ['[b d]]))])
;		  (warehouse/make-warehouse-strips-env 3 4 [1 2] false {0 '[b a] 2 '[c]} nil ['[a b c]]))])
;		  (warehouse/make-warehouse-strips-env 4 4 [1 2] false {0 '[b a] 2 '[d] 3 '[c]} nil ['[a b c]]))])


(deftest hierarchical-algorithms
   (doseq [[inst-n rew h env] [*ns-inst* *wh-inst*]
	   cache?      [false true]
	   graph?      [false true]
	   [sf-n alg strict?] [["aha" aha-star-search true] ["ahss-inf" ahss-search false] ["ahss-=" #(ahss-search % rew) true]]]
     (testing (str inst-n " " cache? " " graph? " " sf-n)
;       (println inst-n cache? graph? sf-n)
       (is ((if strict? = >=) rew  
	 (second (envs/check-solution env (alg (alts/alt-node (get-hierarchy h env) {:cache? cache? :graph? graph?})))))))))

 


  
