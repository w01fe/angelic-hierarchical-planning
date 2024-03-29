(ns angelic.old.envs.strips.test-smart-csps
 (:use clojure.test angelic.old.envs.strips.smart-csps)
 (:import [java.util HashMap Map ArrayList])
 (:require [angelic.util :as util] 
	   [angelic.old.envs :as envs]	   
	   [angelic.old.angelic :as angelic]
	   [angelic.old.angelic.dnf-valuations :as dv]
	   )
 )

       
(defmethod envs/expected-domain-size ::DummyEnv [env pred ind inst-ind] 1)
(def *dummy-env* {:class ::DummyEnv})

(deftest test-smart-csp
  (is 
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b]} #{['bap :a :b]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4}} 
			  {'boo '[[boo 1 3] [boo 1 4] [boo 2 3]] 'bap '[[bap 1 3]]} *dummy-env*)
	{:c 5}
	[[{} {}]]))
      #{{:a 1 :b 4} {:a 2 :b 3}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo] ['bee :a]} #{['bap]} 
			  {}
			  {:a #{1 2 3 4 5}}
			  {} *dummy-env*)
	{}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation 
	  {'{[boo] :unknown [bap] :unknown [bee 1] :unknown} 0 
	    '{[bee 1] :true [bee 2] :unknown [bee 3] :true} 0
	    '{[bap] :true [bee 2] :true [bee 3] :true [bee 4] :true} 0
	    '{[boo] :true [bap] :unknown [bee 5] :unknown} 0}))))
      #{{:a 1} {:a 5}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo] ['bee :a]} #{['bap]} 
			  {}
			  {:a #{1 2 3 4 5} :b #{7 8}}
			  {} *dummy-env*)
	{}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation
	  {'{[boo] :unknown [bap] :unknown [bee 1] :unknown}  0
	    '{[bee 1] :true [bee 2] :unknown [bee 3] :true} 0
	    '{[bap] :true [bee 2] :true [bee 3] :true [bee 4] :true} 0
	    '{[boo] :true [bap] :unknown [bee 5] :unknown} 0}
	  ))))
      #{{:a 1 :b 7} {:a 5 :b 7} {:a 1 :b 8} {:a 5 :b 8}}))
  (is
   (= (set 
       (get-smart-csp-solutions 
	(create-smart-csp #{['boo :a :b] ['bee :a :d] ['box :d]} #{['bap :a :b] ['biz :a :b] ['bat :a :b :d]} 
			  {:c #{5 6}}
			  {:a #{1 2} :b #{3 4 5} :d #{4 5 6}} 
			  {'boo '[[boo 1 3] [boo 1 4] [boo 2 3] [boo 2 5] [boo 1 5]] 'bap '[[bap 1 3]]}
			  *dummy-env*)
	{:c 5}
	(angelic/valuation->pred-maps 
	 (dv/make-dnf-valuation ::dv/DNFValuation
	  {'{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 4] :true [box 5] :true [biz 1 5] :true [biz 2 5] :true [biz 1 4] :unknown [bat 1 5 4] :true} 0 
	    '{[bee 1 4] :true [bee 2 5] :unknown [bee 1 6] :true [box 6] :unknown [biz 1 5] :unknown [biz 2 5] :true [biz 1 4] :unknown} 0}
	  ))))
      #{{:a 1 :b 4 :d 4} {:a 2 :b 3 :d 5} {:a 1 :b 4 :d 6} {:a 1 :b 5 :d 6}})))
      
		  


