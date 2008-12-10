(in-package asdf)
			 
(asdf:defsystem "angel" :components
  nil
  )

(in-package cl-user)


#|
(asdf:defsystem "angel"
    :components 
      ((:module "misc" :pathname "misc/" :serial t
			  :components
			  ((:file "util-pkg")
			   (:file "macros")
			   (:file "clone")
			   (:file "canonicalize" :depends-on ("clone"))
			   (:file "cluster")
			   (:file "help")
			   (:file "utils" :depends-on ("clone" "util-pkg"))
			   (:file "array-utils" :depends-on ("utils" "macros"))
			   (:file "list-utils" :depends-on ("utils"))
			   (:file "hash-utils" :depends-on ("utils"))
			   (:file "function-utils")
			   (:file "exp-utils")
			   (:file "math-utils" :depends-on ("utils"))
			   (:file "matlab" :depends-on ("utils"))
			   (:file "sequence-utils" :depends-on ("utils"))
			   (:file "string-utils" :depends-on ("sequence-utils"))
			   ))
		 
		 (:module "external"
			  :components
			  ((:module "ltk"
				    :components ((:file "ltk")))))
		 
		 (:module "set" :pathname "data-struct/set/"
			  :depends-on ("misc")
			  :components ((:file "set")
				       (:file "seq-set" :depends-on ("set"))
				       (:file "hash-set" :depends-on ("set"))
				       (:file "number-set" :depends-on ("set"))
				       (:file "indexed-set" :depends-on ("set"))
				       (:file "recursive-enumeration" :depends-on ("set"))
				       (:file "named-sets" :depends-on ("set"))
				       (:file "inst-var-accessors" :depends-on ("set"))
				       (:file "create-sets" :depends-on ("set" "indexed-set" "inst-var-accessors"))
				       (:file "interval" :depends-on ("set"))
				       (:file "directory-set" :depends-on ("set"))
				       (:file "direct-product-set" :depends-on ("set" "inst-var-accessors"))))
		 
		 (:module "mapping" :pathname "data-struct/"
			  :depends-on ("misc" "set")
			  :components
			  ((:file "mapping")))

		 (:module "data-struct" :pathname "data-struct/"
			  :depends-on ("misc" "prob" "set" "mapping")
			  :components
			  ((:file "bucketed-counts")
			   (:file "circular-vector")
			   (:file "local-search")
			   (:file "queue")
			   (:file "bst" :depends-on ("tree"))
			   (:file "priority-queue")
			   (:module "graph"
				    :depends-on ("queue" "priority-queue" "union-find")
				    :components
				    ((:file "graph")
				     (:file "topological-sort" :depends-on ("graph"))
				     (:file "adjacency-list-graph" :depends-on ("graph"))
				     (:file "adjacency-matrix-graph" :depends-on ("graph"))
				     (:file "algorithms" :depends-on ("graph"))
				     (:file "connected-components" :depends-on ("graph"))
				     (:file "flow" :depends-on ("adjacency-list-graph"))))
			   (:module "bnet"
				    :depends-on ("graph")
				    :components ((:file "bnet-pkg")
						 (:file "2tbn" :depends-on ("bnet-pkg"))
						 (:file "structure-learning" :depends-on ("2tbn"))))
			   (:module "tree"
				    :components ((:file "tree")
						 (:file "tree-set" :depends-on ("tree"))))
			   
			   (:file "union-find" :depends-on ("tree"))
			   
			   (:module "prop-logic" :depends-on ("tree")
				    :components ((:file "prop-formula")
						 (:file "dnf" :depends-on ("prop-formula"))
						 (:file "dnf-set" :depends-on ("dnf"))))
			   
 			   (:module "pot-set"
 				    :components ((:file "pot-pkg")
						 (:file "operation" :depends-on ("pot-pkg"))
 						 (:file "potential" :depends-on ("pot-pkg"))
 						 (:file "tabular-potential" :depends-on ("potential"))
 						 (:file "function-potential" :depends-on ("potential"))
						 (:file "number-potential" :depends-on ("potential"))
					 	 (:file "pot-set" :depends-on ("potential" "operation"))
						 (:file "undirected-graphical-model" :depends-on ("pot-set"))
						 ))

			   (:file "cache")
			   ))
		 
		 
		 (:module "env" :depends-on ("misc" "set" "prob")
			  :components ((:file "env-pkg")
				       (:file "env" :depends-on ("env-pkg"))
				       (:file "fully-observable-env" :depends-on ("env"))
				       (:file "trajectory" :depends-on ("env"))
				       ))
		 
		 (:module "fn-approx" :pathname "fn-approx/"
			  :depends-on ("misc")
			  :components ((:file "fn-approx")
				       (:file "tabular-fn-approx" :depends-on ("fn-approx"))
				       (:file "linear-fn-approx" :depends-on ("fn-approx"))
				       (:file "linear-fn-approx-with-bounds" :depends-on ("fn-approx"))))
		 
		 (:module "rl-functions"
			  :depends-on ("fn-approx" "misc" "data-struct" "prob" "math" "mdp")
			  :components ((:module "value-function" :depends-on ("policy")
						:components ((:file "value-function")
							     (:file "tabular-value-function" :depends-on
								    ("value-function"))))
				       
						
				       (:module "q-function"
						:depends-on ("value-function" "policy")
						:components ((:file "q-function")
 							     (:module "crl" :depends-on ("q-function")
 								      :components
 								      ((:file "crl-q-function")
 								       (:file "crl-features"
 									      :depends-on 
									      ("crl-q-function"))))
							     (:file "sum-q-function" 
								    :depends-on ("q-function"))
							     (:file "approx-q-function" :depends-on 
								    ("q-function"))
							     (:file "tabular-q-function" :depends-on
								    ("q-function"))
							     (:module "decomposed" :depends-on ("crl")
								      :components
								      ((:file "decomposed-q-function")
								       (:file "decomposed-crl-q-function")
								       (:file "decomposed-tabular-q-function")))
							     (:file "env-q-function" :depends-on 
								    ("approx-q-function"))
							     ))
				       
				       (:module "policy"
						:components ((:file "policy")
							     
							     (:file "random-policy" :depends-on ("policy"))
							     (:file "tabular-policy" :depends-on ("policy"))
							     (:file "prompt-policy" :depends-on ("policy"))
							     ))
				       
				       (:module "policy2" :depends-on ("q-function" "policy")
						:pathname "policy/"
						:components ((:file "greedy-policy")
							     (:module "exp-pol"
								      :components
								      ((:file "exploration-policy")))))
				       
				       (:module "advantage-function" :depends-on ("value-function" "policy")
						:components ((:file "advantage-function")
							     (:file "tabular-advantage-function"
								    :depends-on ("advantage-function"))
							     (:file "sum-advantage-function"
								    :depends-on ("advantage-function"))))


				       (:module "learning-rate"
						:components ((:file "learning-rate")
							     (:file "polynomial-learning-rate" 
								    :depends-on ("learning-rate"))))))
		 
		 (:module "math" :pathname "math/" :depends-on ("misc" "set" "external")
			  :components ((:file "lin-alg")
				       (:file "chi-square")
				       (:file "svd" :depends-on ("lin-alg"))
				       ))
		 
		 (:module "geometry"
			  :depends-on ("math" "prob") :pathname "math/geometry/"
			  :components
						((:file "geometry")
						 (:module "transform" :depends-on ("geometry")
							  :components
							  ((:file "transformation")
							   (:file "rigid-2d" :depends-on ("transformation"))))
						 (:module "point-sets" :depends-on ("transform")
							  :components
							  ((:file "point-sets")
							   (:file "discrete" :depends-on ("point-sets"))
							   (:file "sphere" :depends-on ("point-sets"))
							   (:file "polygon" :depends-on ("point-sets" "sphere"))
							   ))
						 (:module "conf-sets" :depends-on ("point-sets" "transform")
							  :components
							  ((:file "conf-set")
							   (:file "rigid-2d-motions" :depends-on ("conf-set"))))
						 (:file "geom-language" :depends-on ("transform" "point-sets"))
						 (:module "algorithms" :depends-on ("point-sets" "transform")
							  :components
							  ((:file "general")))
						 (:file "ltk" :depends-on ("point-sets" "transform"))
						 ))
		 
		 (:module "motion-planning" :depends-on ("math" "prob" "geometry")
			  :components ((:file "motion-planning")
				       (:module "cspace"
						:depends-on ("motion-planning")
						:components
						((:file "cspace")
						 (:file "simple-cs" :depends-on ("cspace"))
						 (:file "cspace-family" :depends-on ("simple-cs"))))
				       (:module "geometric"
						:depends-on ("motion-planning")
						:components
						((:file "visibility")))
				       (:module "roadmap"
						:depends-on ("cspace")
						:components 
						((:file "roadmap")
						 (:file "visibility" :depends-on ("roadmap"))
						 (:file "simple" :depends-on ("roadmap"))))))
		 
		 (:module "prob"
			  :depends-on ("set" "mapping" "math")
			  :components ((:file "probability-distribution")
				       (:file "function-random-variable" :depends-on ("probability-distribution"))
				       (:file "information-theory" :depends-on ("probability-distribution"))
				       (:file "create-distributions" :depends-on ("probability-distribution"))
				       (:file "vector-probability-distribution" :depends-on ("probability-distribution"))
				       (:file "hash-table-prob-dist" :depends-on ("probability-distribution"))
				       (:module "temporal"
						:components ((:file "state-space-model")
							     )
						:depends-on ("probability-distribution"))
				       (:module "parametric"
						:depends-on ("probability-distribution")
						:components ((:file "uniform")
							     (:file "gaussian")))
				       (:module "filtering"
						:depends-on ("probability-distribution" "temporal")
						:components					
						((:file "filtering")
						 (:module "dmcmc"
							  :depends-on ("filtering" "exact")
							  :components
							  ((:file "dmcmc")
							   (:file "dmcmc-filter" :depends-on ("dmcmc" "decay"))
							   (:file "decay" :depends-on ("dmcmc"))
							   (:file "run-dmc" :depends-on ("dmcmc-filter"))
							   (:file "observer" :depends-on ("dmcmc"))))
						 (:module "pf"
							  :depends-on ("filtering")
							  :components 
							  ((:file "pf")))
						 (:module "exact"
							  :depends-on ("filtering")
							  :components
							  ((:file "exact")))
						 (:module "exp"
							  :depends-on ("dmcmc" "exact" "pf")
							  :components
							  ((:file "dmcmc-scaling")))))
				       (:file "alist-probability-distribution" :depends-on ("probability-distribution"))))
		 
		      
		 (:module "mdp" :depends-on ("env" "data-struct" "math" "prob" "misc")
			  :in-order-to ((compile-op (load-op "misc")))						   
			  :components ((:file "mdp-pkg")
				       (:file "smdp"
					      :depends-on ("mdp-pkg"))
				       (:file "mdp"
					      :depends-on ("smdp"))
				       (:file "mdp-env"
					      :depends-on ("mdp"))
				       (:file "2tbn-mdp-env"
					      :depends-on ("mdp-env"))
				       (:file "tabular-smdp"
					      :depends-on ("smdp"))
				       (:file "hierarchical-smdp"
					      :depends-on ("smdp" "tabular-smdp"))
				       (:file "tabular-mdp" :depends-on ("mdp"))
				       (:file "sparse-mdp" :depends-on ("mdp"))))
     
		 (:module "dp" :depends-on ("mdp" "data-struct" "misc" "math" "rl-functions")
			  :components ((:file "dp")
				       (:file "mdp-dp" :depends-on ("dp"))
				       (:file "sparse-dp" :depends-on ("mdp-dp"))
				       (:file "hierarchical-dp" :depends-on ("dp" "sparse-dp"))
				       (:file "markov-chain" :depends-on ("dp"))
				       ))
     
		 (:module "rl" :depends-on ("mdp" "data-struct" "misc" "env" "rl-functions" "dp" "external")
			  :components ((:file "reinforcement-learning")
				       (:file "rl-observer" :depends-on ("reinforcement-learning"))
				       (:file "rl-control" :depends-on ("rl-observer" "reinforcement-learning"))
				       (:file "rl-user" :depends-on ("reinforcement-learning" "rl-observer" 
											      "rl-control" "obs"))
				       (:module "obs"
						:depends-on ("rl-observer")
						:components ((:file "progress-printer")
							     (:file "stat-gatherer")
							     (:file "message-logger")
							     (:file "trajectory-gatherer")
							     (:file "env-observer")
							     (:file "ltk-observer")))
				       (:module "learn"
						:depends-on ("obs")
						:components ((:file "learning-algorithm")
							     (:file "q-learning" :depends-on ("learning-algorithm"))
							     (:file "advantage-updating" :depends-on ("learning-algorithm"))
							     (:file "decomposed-advantage-updating"
								    :depends-on ("advantage-updating"))
							     (:file "decomposed-q-learning" :depends-on
								    ("q-learning"))
							     (:file "approximate-policy-iteration"
								    :depends-on ("learning-algorithm"))
							     (:file "gold-standard" :depends-on ("learning-algorithm"))
							     (:file "certainty-equivalence" :depends-on ("learning-algorithm"))
							     ))))
		 
		 (:module "boltzmann-exploration" :depends-on ("rl" "rl-functions" "prob")
			  :pathname "rl-functions/policy/exp-pol/"
			  :components ((:file "boltzmann-exp-pol")
				       (:file "epsilon-boltzmann-exp-pol" :depends-on ("boltzmann-exp-pol"))))


		 
		 (:module "envs" :depends-on ("misc" "data-struct" "mdp" "math")
			  :components ((:file "grid-world")
				       (:file "maze-mdp" :depends-on ("grid-world"))
				       (:file "variable-effector-env")
				       (:module "res-balance" :depends-on ("grid-world")
						:components ((:file "rbe-2tbn")))
				       (:module "flags" :depends-on ("grid-world")
						:components ((:file "flags")))
				       (:module "othello"
						:components ((:file "othello")
							     (:file "policies" :depends-on ("othello"))
							     (:file "interface" :depends-on ("othello"))
							     (:file "othello-env" :depends-on ("othello"))
							     (:file "features" :depends-on ("othello"))))
				       (:module "taxi"
						:depends-on ("grid-world")
						:components ((:file "td-taxi-env")
							     (:file "td-taxi-examples")
							     (:file "td-taxi-flat-lfa" :depends-on ("td-taxi-env"))
							     (:file "qe-taxi")
							     ))))
     
			    

		 (:module "alisp" :in-order-to ((compile-op (load-op "misc")))
			  :depends-on ("misc" "env" "data-struct" "rl-functions" "rl" "dp")
			  :components ((:file "alisp")
				       (:file "alisp-state" :depends-on ("alisp"))
				       (:file "alisp-observer" :depends-on ("alisp"))
				       (:file "alisp-program" :depends-on ("alisp"))
				       (:file "rlm" :depends-on ("alisp" "alisp-observer" "alisp-program" "alisp-state"))
				       (:file "alisp-user" :depends-on ("alisp" "rlm" "alisp-program" 
										"obs" "alisp-observer"))
				       
				       (:module "rl-functions" :depends-on ("alisp" "alisp-state")
						:components ((:file "alisp-approx-q-function")
							     (:file "alisp-features")
							     (:file "exit-distribution")
							     (:file "array-exit-distribution"
								    :depends-on ("exit-distribution"))))
					      
				       (:module "obs"
						:depends-on ("alisp" "alisp-observer")
						:components ((:file "alisp-io-int-observer")
							     (:file "progress-printer")))
				       
				       (:module "learn"
						:depends-on ("alisp" "alisp-observer" "rl-functions")
						:components ((:file "learning-algorithm")
							     (:file "gold-standard" :depends-on ("learning-algorithm"))
							     (:file "hordq" :depends-on ("learning-algorithm"))
							     (:file "rordq" :depends-on ("hordq"))
							     (:file "smdpq" :depends-on ("learning-algorithm"))))
				       ))
		 
		 
		 

 		 
 		 
		 
		 
		 (:module "maxq" :depends-on ("alisp")
			  :in-order-to ((compile-op (load-op "alisp")))
			  :components
			  ((:file "maxq-hierarchy")
			   (:file "task-learner" :depends-on ("maxq-hierarchy"))
			   (:file "var-specs")
			   (:file "parse-trajectory" :depends-on ("maxq-hierarchy"))
			   (:file "goal-language" :depends-on ("maxq-hierarchy"))
			   (:file "greedy-hierarchy-construction" 
				  :depends-on ("maxq-hierarchy" "parse-trajectory" "goal-language" "var-specs"))
			   (:file "relevant-variables"
				  :depends-on ("maxq-hierarchy" "var-specs"))
			   ))

		 
		 (:module "alisp-examples" :depends-on ("env" "envs" "alisp" "misc" "maxq")
			  :in-order-to ((compile-op (load-op "alisp")))
			  :components
			  ((:module "taxi" :components ((:file "td-taxi-prog")
							(:file "td-taxi-prog-features" 
							       :depends-on ("td-taxi-prog"))
							(:file "taxi-maxq")
							(:file "qe-taxi-prog")))))
		 
		 (:module "autoshape" :depends-on ("rl")
			  :components
			  ((:file "autoshape")
			   (:file "pot-fn-learner" :depends-on ("autoshape"))
			   (:file "autodec" :depends-on ("autoshape"))
			   (:file "option")))


		 (:module "test" :depends-on ("envs" "misc")
			  :components ((:file "mdp-test-envs")))))
	

(asdf:defsystem "calisp"
    :depends-on ("hrl")
    :components ((:module "misc" :serial t
			  :components
			  ((:file "socket-utils")
			   (:file "threads")))
		 (:module "data-struct" :depends-on ("misc")
			  :components
			  ((:file "condition-variable")))
		 (:module "stratagus-env" :depends-on ("misc" "data-struct")
 			  :pathname "envs/stratagus/" :serial t
 			  :components ((:file "gameinfo")
				       (:file "stratagus-env-pkg")
 				       (:file "strat-constants")
 				       (:file "strat-env-state")
 				       (:file "stratagus-env")
				       ))
		 (:module "concurrent-alisp"
 			  :depends-on ("misc" "data-struct")
 			  :components ((:file "calisp")
 				       (:file "calisp-observer" :depends-on ("calisp"))
				       (:module "rl-functions" :depends-on ("calisp")
						:components ((:file "q-function")
							     (:file "calisp-features")
							     (:file "crl-q-function" :depends-on ("calisp-features"))
							     ))
				       (:module "obs"
						:depends-on ("calisp" "calisp-observer")
						:components ((:file "calisp-io-int-observer")
							     (:file "message-logger")
							     (:file "thread-debugger")))
				       (:module "learn"
						:depends-on ("rl-functions" "obs")
						:components ((:file "smdpq")
							     (:module "decomposed"
								      :components
								      ((:file "threadwise-decomposed-q")
								       (:file "temporally-decomposed-q")
								       (:file "reward-decomposition-debugger")))))
 				       (:file "calisp-state" :depends-on ("calisp"))
 				       (:file "calisp-program" :depends-on ("calisp" "calisp-state"))
 				       (:file "crlm" :depends-on ("calisp-program"))
				       (:file "calisp-user" :depends-on ("crlm" "learn"))))
		 
		 (:module "calisp-examples" :in-order-to ((compile-op (load-op "concurrent-alisp")))
			  :depends-on ("misc" "concurrent-alisp")
			  :components
			  ((:module "res-balance" :components ((:file "rbe-prog")
							       (:file "rbe-progs")
							       (:file "rbe-tabular-features"
								      :depends-on ("rbe-prog"))
							       (:file "rbe-linear-features"
								      :depends-on ("rbe-prog"))
							       (:file "rbe-dec"
								      :depends-on ("rbe-prog"))))
			   (:module "ve-env" :components ((:file "ve-prog1")))))))




(asdf:defsystem "local"
    :components ((:module "exec" :pathname "misc/"
			  :components
			  ((:file "exec")))))

|#


