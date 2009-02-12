(ns edu.berkeley.ai.domains.timing-nav-switch
 (:require [edu.berkeley.ai [util :as util] [envs :as envs] [search :as search] [angelic :as angelic]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips]
	   [edu.berkeley.ai.domains.nav-switch :as nav-switch]
	   [edu.berkeley.ai.search.algorithms.textbook :as textbook]
	   [edu.berkeley.ai.angelic [dnf-simple-valuations :as dnf-simple-valuations]
	                            [hierarchies :as hierarchies]]
	   [edu.berkeley.ai.angelic.hierarchies.strips-hierarchies :as strips-hierarchies]
	   )
 )

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
      "constant simplified" strips/constant-predicate-simplify-strips-planning-instance, 
      "constant simplified, flat" (comp strips/flatten-strips-instance
					strips/constant-predicate-simplify-strips-planning-instance)})

(defn- time-and-check-hierarchical [str reward hierarchy-schema env val-type simplifier]
  (println str)
  (let [initial-hla (simplifier (hierarchies/instantiate-hierarchy hierarchy-schema env))
		node (hierarchies/make-initial-top-down-forward-node val-type initial-hla)]
  (util/assert-is 
   (= reward (second (envs/check-solution (hierarchies/hla-environment initial-hla)
     (time 
      (*search-fn* node
       ))))))))

(def *strips-hierarchy-simplifiers*
     {"ungrounded" identity,
      "smart" #(strips-hierarchies/constant-simplify-strips-hierarchy %
		    strips/dont-constant-simplify-strips-planning-instance), 
      "smart, constant simplified" #(strips-hierarchies/constant-simplify-strips-hierarchy %
	    strips/constant-predicate-simplify-strips-planning-instance),
     "grounded" #(strips-hierarchies/ground-and-constant-simplify-strips-hierarchy %
		    strips/dont-constant-simplify-strips-planning-instance), 
     "grounded, constant simplified" #(strips-hierarchies/ground-and-constant-simplify-strips-hierarchy %
	    strips/constant-predicate-simplify-strips-planning-instance)})


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
  ::angelic/ExplicitValuation identity)
  
(doseq [[name simplifier] *strips-simplifiers*]
  (time-and-check-hierarchical (format  "5x5 flat-hierarchy, strips, %s, 0 heuristic" name) 
    *small-ns-reward*
    (hierarchies/make-flat-hierarchy-schema (constantly 0))    
    (simplifier  (apply nav-switch/make-nav-switch-strips-env *small-ns-args*))
    ::angelic/ExplicitValuation identity))

(doseq [[name simplifier] *strips-hierarchy-simplifiers*]
  (time-and-check-hierarchical (format  "5x5 flat-strips-hierarchy, %s, 0 heuristic" name) 
    *small-ns-reward*
    (strips-hierarchies/make-flat-strips-hierarchy-schema 
     (nav-switch/make-nav-switch-strips-domain) (constantly 0))    
    (apply nav-switch/make-nav-switch-strips-env *small-ns-args*)
    ::dnf-simple-valuations/DNFSimpleValuation simplifier))

(doseq [[name simplifier] *strips-hierarchy-simplifiers*]
  (time-and-check-hierarchical (format  "6x6 flat-strips-hierarchy, %s, 0 heuristic" name) 
    *big-ns-reward*
    (strips-hierarchies/make-flat-strips-hierarchy-schema 
     (nav-switch/make-nav-switch-strips-domain) (constantly 0))    
    (apply nav-switch/make-nav-switch-strips-env *big-ns-args*)
    ::dnf-simple-valuations/DNFSimpleValuation simplifier))

  )
;;;; On to heuristics.
;; TODO: graph search

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
    (apply nav-switch/make-nav-switch-strips-env *huge-ns-args*)
    ::dnf-simple-valuations/DNFSimpleValuation simplifier))


(doseq [[name simplifier]  (take 3 *strips-hierarchy-simplifiers*)]
  (time-and-check-hierarchical (format  "square %s strips-hierarchy, %s, heuristic" *huge-ns-size* name) 
    *huge-ns-reward*
    (hierarchies/parse-hierarchy "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/nav_switch2.hierarchy" 
     (nav-switch/make-nav-switch-strips-domain)) 
    (apply nav-switch/make-nav-switch-strips-env *huge-ns-args*)
    ::dnf-simple-valuations/DNFSimpleValuation simplifier))
 )