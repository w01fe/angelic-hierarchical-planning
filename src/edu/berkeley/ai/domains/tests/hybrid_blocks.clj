(ns edu.berkeley.ai.domains.tests.hybrid-blocks
 (:use clojure.test 
       edu.berkeley.ai.domains.hybrid-blocks
       )
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.search.algorithms.textbook :as algs]
           [edu.berkeley.ai.search.state-space :as ss]
           [edu.berkeley.ai.envs.hybrid-strips :as hs])
 )



(deftest simple-hybrid-test
  (let [env (make-hybrid-blocks-strips-env 7 7 [2 2] '[[a 1 1 2 2] [b 4 1 2 2]] '[[b [[a]]]])] ;test progression. 
    (is 
     (envs/satisfies-condition?  
       (envs/safe-apply-actions (envs/get-initial-state env)
	  [(hs/get-hs-action env 'get '{?b a ?c table})
	   (hs/get-hs-action env 'up-holding '{?b a ?ngy 4})
	   (hs/get-hs-action env 'right-holding '{?b a ?ngx 5})
	   (hs/get-hs-action env 'put '{?b a ?c b})])
       (envs/get-goal env))))
  (let [args  '[10 4 [1 1] [[a 1 3 6 1] [b 7 1 2 1 [[c 0 1 2 2]]]] [[a [[b] [c]]]]]] ; test solution, split points/discrete/
    (doseq [[e s] (map vector (map #(apply make-hybrid-blocks-strips-env %) [args (conj args 1)]) [-39 -33] #_ [-75 -69])]
      (is (= s (second (algs/a-star-graph-search (ss/ss-node e))))))))

