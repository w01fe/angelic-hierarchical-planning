(ns edu.berkeley.ai.domains.nav-regions
 (:require [edu.berkeley.ai [util :as util] [envs :as envs]] 
           [edu.berkeley.ai.envs.states :as states]
           [edu.berkeley.ai.domains.strips :as strips]
           [edu.berkeley.ai.angelic.hierarchies :as hierarchies]	  
           [edu.berkeley.ai.angelic :as angelic]	  
	   )
 )


(def *sqrt2* (Math/sqrt 2))
(def *nav-actions*
     {'left  [-1  0 -1]
      'right [ 1  0 -1]
      'up    [ 0 -1 -1]
      'down  [ 0  1 -1]
      'ul    [-1 -1 (- *sqrt2*)]
      'ur    [ 1 -1 (- *sqrt2*)]
      'dl    [-1  1 (- *sqrt2*)]
      'dr    [ 1  1 (- *sqrt2*)]})
      


(defn make-nav-regions-env 
  "Region-fn returns # > 0 for region, 0 for blocked. Must have blocked borders.
   Region-connectors is map from region # to [my-pt your-pt].
   Connector-dists is map from c-pt to [oc-pt dist]"
  [region-fn region-connectors connector-targets connector-dists [init-x init-y] [goal-x goal-y]]
  (let [init [init-x init-y]
	goal [goal-x goal-y]
	actions 
      (cons 
       (envs/make-action 'connect
	 (fn [p] [(util/safe-get connector-targets p) -1.0])
	 (envs/make-simple-condition #(find connector-targets %)))
       (for [[name [dx dy c]] *nav-actions*]
	(let [dx (int dx) dy (int dy) c (double c)]
	  (envs/make-action name 
	    (fn [[x y]] (let [x (int x) y (int y)] [[(+ x dx) (+ y dy)] c]))
	    (envs/make-simple-condition 
	     (fn [[x y]] (let [x (int x) y (int y) nx (int (+ x dx)) ny (int (+ y dy))]
			   (= (region-fn [x y]) (region-fn [nx ny])))))))))]
    (util/assert-is (> (region-fn init) 0))
    (util/assert-is (> (region-fn goal) 0))
    (assoc (envs/make-environment 
	    init
	    (states/make-state-set str)
	    (envs/make-enumerated-action-space actions)
	    (envs/make-simple-condition #(= % goal) true))
      :region-fn region-fn
      :region-connectors region-connectors
      :connector-dists   connector-dists
      :connector-targets connector-targets
      :init-pos [init-x init-y]
      :goal-pos [goal-x goal-y]
      :actions  (into {} (map #(vector (:name %) %) actions))
      )))


(defn make-nav-regions-heuristic [[goal-x goal-y]]
  (let [goal-x (int goal-x) goal-y (int goal-y)]
    (fn [[cur-x cur-y]]
      (let [cur-x (int cur-x) cur-y (int cur-y)]
	(let [dx (Math/abs (int (- cur-x goal-x)))
	      dy (Math/abs (int (- cur-y goal-y)))
	      mind (min dx dy)
	      resd (- (max dx dy) mind)]
	  (- 0 (* mind *sqrt2*) resd))))))
  

(util/deftest test-nav-regions
  (doseq [h [nil [(make-nav-regions-heuristic [10 2])]]]
    (util/is (= '[dr ur connect right connect right right right dr]
	 (map :name 
	   (first 
	    (edu.berkeley.ai.search.algorithms.textbook/a-star-graph-search 
	     (apply edu.berkeley.ai.search/ss-node
  	     (concat [(make-nav-regions-env 
	      (fn [[x y]]
		(([[0 0 0 0 0 0 0 0 0 1 0 0]
		   [0 1 0 1 2 2 3 3 3 3 0 0]
		   [0 1 1 1 0 0 0 0 3 0 3 0]
		   [0 0 0 0 0 0 0 0 0 0 0 0]]
		    y) x))
	      {1 [[3 1]] 2 [[4 1] [5 1]] 3 [[6 1]]}
	      {[3 1] [4 1], [4 1] [3 1], [5 1] [6 1], [6 1] [5 1]} 
	      {[4 1] [[[5 1] -1]] [5 1] [[[4 1] -1]]}
	      [1 1] [10 2] )] h)))))))))
	     

; (map :name (first  (a-star-graph-search (edu.berkeley.ai.search/ss-node (make-nav-regions-env (fn [[x y]] (([[0 0 0 0 0 0 0 0 0 1 0 0] [0 1 0 1 2 2 3 3 3 3 0 0] [0 1 1 1 0 0 0 0 0 3 3 0] [0 0 0 0 0 0 0 0 0 0 0 0]] y) x)) {1 [[3 1]] 2 [[4 1] [5 1]] 3 [[6 1]]} {[3 1] [4 1], [5 1] [6 1]} {} [1 1] [10 2] )))))

;; Hierarchy


(derive ::NavRegionsAct            ::NavRegionsHLA)
(derive ::NavRegionsTraverse       ::NavRegionsHLA)
(derive ::NavRegionsTraverseRegion ::NavRegionsHLA)
(derive ::NavRegionsNav            ::NavRegionsHLA)
(derive ::NavRegionsPrimitive      ::NavRegionsHLA)
(derive ::NavRegionsFinish         ::NavRegionsPrimitive)


(defn make-nav-regions-description [[goal-x goal-y]]
  (let [goal-x (int goal-x) goal-y (int goal-y)]
    (angelic/make-explicit-description
     (envs/make-enumerated-action-space
      [(envs/make-action 'dummy    
	(fn [[cur-x cur-y]]
	  [[goal-x goal-y] 
	   (let [cur-x (int cur-x) cur-y (int cur-y)]
	     (let [dx (Math/abs (int (- cur-x goal-x)))
		   dy (Math/abs (int (- cur-y goal-y)))
		   mind (min dx dy)
		   resd (- (max dx dy) mind)]
	       (- 0 (* mind *sqrt2*) resd)))])
	(envs/make-simple-condition (constantly true) true))]))))

(defn make-nav-regions-hierarchy [env]
  (let [finish-desc (angelic/instantiate-description-schema angelic/*finish-description* env)]
    [{:class ::NavRegionsAct :env env 
      :optimistic-description  (make-nav-regions-description (util/safe-get env :goal-pos))
      :pessimistic-description (angelic/parse-description [:pess] nil nil)
      :primitives (util/map-vals 
		   #(let [d (angelic/make-explicit-description
			     (envs/make-enumerated-action-space [%]))]
		     {:class ::NavRegionsPrimitive :env env :primitive %
		      :optimistic-description d :pessimistic-description d})
		   (util/safe-get env :actions))}
     {:class ::NavRegionsFinish :env env :primitive :noop
      :optimistic-description finish-desc
      :pessimistic-description finish-desc}]))


(defn- make-traverse-hla [parent-hla src dst rew]
  (let [desc (angelic/make-explicit-description
	      (envs/make-enumerated-action-space
	       [(envs/make-action 'dummy
		  (fn [[cur-x cur-y]] [dst rew])
		  (envs/make-simple-condition (constantly true) true))]))]
    {:class ::NavRegionsTraverse :env (util/safe-get parent-hla :env)
     :optimistic-description desc :pessimistic-description desc
     :primitives (util/safe-get parent-hla :primitives)
     :src src :dst dst :rew rew}))
 
(defn- make-nav-hla      [parent-hla dst]
  {:class ::NavRegionsNav :env (:env parent-hla)
   :optimistic-description (make-nav-regions-description dst)
   :pessimistic-description (angelic/parse-description [:pess] nil nil)
   :primitives (util/safe-get parent-hla :primitives)
   :dst dst})


(defmethod hierarchies/hla-environment                        ::NavRegionsHLA [hla]
  (util/safe-get hla :env))

(defmethod hierarchies/hla-default-optimistic-valuation-type  ::NavRegionsHLA [hla]
  ::angelic/ExplicitValuation)

(defmethod hierarchies/hla-default-pessimistic-valuation-type ::NavRegionsHLA [hla]
  ::angelic/ExplicitValuation)

(defmethod hierarchies/hla-primitive?  ::NavRegionsHLA       [hla] false)
(defmethod hierarchies/hla-primitive?  ::NavRegionsPrimitive [hla] true)
  
(defmethod hierarchies/hla-primitive   ::NavRegionsHLA       [hla] (:primitive hla))

(defmethod hierarchies/hla-name ::NavRegionsAct       [hla] '[act])
(defmethod hierarchies/hla-name ::NavRegionsTraverse  [hla] ['traverse (:src hla) (:dst hla)])
(defmethod hierarchies/hla-name ::NavRegionsNav       [hla] ['nav (:dst hla)])
(defmethod hierarchies/hla-name ::NavRegionsPrimitive [hla] (:name (:primitive hla)))
(defmethod hierarchies/hla-name ::NavRegionsFinish    [hla] '[finish])

(defmethod hierarchies/hla-hierarchical-preconditions ::NavRegionsHLA [hla] 
  envs/*true-condition*)

; hierarchy : nav (square/connector)
;           : traverse (from in-connector to out-connector)

; initial-plan: either nav(dst) or nav(some conn), traverse(some final conn), nav(dst)

(defmethod hierarchies/hla-immediate-refinements 
  [::NavRegionsAct ::angelic/ExplicitValuation]            [hla opt-val]
  (let [cpos (util/safe-singleton (keys (angelic/explicit-valuation-map opt-val)))
	env  (:env hla)
	connect (util/safe-get-in hla [:primitives 'connect])
	{:keys [goal-pos region-fn region-connectors connector-dists connector-targets]} env]
    (concat
     (when (= (region-fn cpos) (region-fn goal-pos))
       [[(make-nav-hla hla goal-pos)]])
     (if (find connector-targets cpos)  ; already at connector
         (for [[connector rew] (connector-dists cpos)]
	   [(make-traverse-hla hla cpos connector rew) connect hla])
       (for [connector (region-connectors (region-fn cpos))]
	 [(make-nav-hla hla connector) connect hla])))))


(defmethod hierarchies/hla-immediate-refinements 
  [::NavRegionsTraverse ::angelic/ExplicitValuation]       [hla opt-val]
  [[(make-nav-hla hla (util/safe-get hla :dst))]])

(defmethod hierarchies/hla-immediate-refinements
  [::NavRegionsNav ::angelic/ExplicitValuation]            [hla opt-val]
  (let [cpos (util/safe-singleton (keys (angelic/explicit-valuation-map opt-val)))]
    (if (= cpos (util/safe-get hla :dst))
        [[]] ;; ???
      (for [action (envs/applicable-actions cpos (envs/get-action-space (:env hla)))
	    :when (not (= (:name action) 'connect))]
	[(util/safe-get-in hla [:primitives (:name action)])
	 hla]))))  

(defmethod hierarchies/hla-optimistic-description             ::NavRegionsHLA [hla]
  (util/safe-get hla :optimistic-description))

(defmethod hierarchies/hla-pessimistic-description            ::NavRegionsHLA [hla]
  (util/safe-get hla :pessimistic-description))


(util/deftest test-nav-regions-hierarchy
  (util/is (= '[dr ur connect right connect right right right dr]
       (map :name 
	   (first 
	    (edu.berkeley.ai.angelic.hierarchies.offline-algorithms/aha-star-search 
	     (edu.berkeley.ai.angelic.hierarchies.abstract-lookahead-trees/alt-node
	       (make-nav-regions-hierarchy  
		(make-nav-regions-env 
		 (fn [[x y]]
		   (([[0 0 0 0 0 0 0 0 0 1 0 0]
		      [0 1 0 1 2 2 3 3 3 3 0 0]
		      [0 1 1 1 0 0 0 0 3 0 3 0]
		      [0 0 0 0 0 0 0 0 0 0 0 0]]
		       y) x))
		 {1 [[3 1]] 2 [[4 1] [5 1]] 3 [[6 1]]}
		 {[3 1] [4 1], [4 1] [3 1], [5 1] [6 1], [6 1] [5 1]} 
		 {[4 1] [[[5 1] -1]] [5 1] [[[4 1] -1]]}
		 [1 1] [10 2] )))))))))
