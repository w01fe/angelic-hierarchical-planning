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
;Infrastructure:
; - Job format
; - Cluster framework
;)


;experiments
; - Offline
;    - Incl. various offline and online 
;    - Grounded STRIPS (+heuristic)
;    - Flat-strips hierarchy (+heuristic)
;    - Real hierarchy (pick1)
; - Online;
;
; - Things to measure
;   - startup time
;   - time
;   - memory (?)
;   - number of refinements/expansions
;   - number of next-states/progressions 
;
;- Cluster framework?
;  - Given set of jobs, (cartesian product?), folder location, number,
;  - ... do this job (after warmups)
;   - Clojure launcher for cluster run would be nice
;   - One potential hitch: dependencies between jobs
;      - May have lattice, if one job times out, don't bother with more
;         difficult jobs.  Only within runs on a single machine?  Then,
;         need way to specify granularity of batching, ...
;

;Missing things in experiments
; - Support for old graph (done)
; - Support for singleton-only graph (?)

; Weighted ICAPS fn.

; Guided and unguided hierarchies.

