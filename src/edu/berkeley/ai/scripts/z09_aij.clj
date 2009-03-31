(ns edu.berkeley.ai.scripts.z09-aij
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains [strips :as strips] [nav-switch :as nav-switch] [warehouse :as warehouse]]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-simple-valuations :as dnf-simple-valuations]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies [strips-hierarchies :as strips-hierarchies] 
	    [abstract-lookahead-trees :as alts] [offline-algorithms :as offline]
	    [online-algorithms :as online]]
	   [edu.berkeley.ai.scripts.experiments :as experiments]
	   )
 )

; hfs won't work with road trip .....

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
			~(:ref-choice m)))
     (fn [m] #_ (println m) `(envs/solution-name (~(:algorithm m) ~'init))))
    'edu.berkeley.ai.scripts.z09-aij
    nil
    20
    512
    nil
    experiments/*planning-experiment-result*))
			      

; (make-experiment-set "test" (parameter-set-tuples '[:product [:x [1 2]] [:y [3 4]]] (fn [m] (:x m)) (fn [m] `(+ ~'init ~(:y m)))) 'user nil 2 1 nil *simple-experiment-result*))  


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
; - AHLRTA*  (max-refs, HLAs)
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

)

