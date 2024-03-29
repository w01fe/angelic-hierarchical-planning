; A node implementation for forward state-space search on an deterministic, FO, countable environment with finite action space.
; Two versions are possible: produce primitive refinements or not.  
;   Now, this version does not.  Old version that does is below.
;   (if you want that, use flat hierarchy?)

; The currently implemented version of consistency enforcement is incorrect. 
; See Mero 1984.  In fact, it can't be done without reopening nodes.  See http://www.ise.bgu.ac.il/faculty/felner/research/incaaai.pdf.  So, forget it.  

(ns angelic.old.search.state-space
   (:use angelic.old.search)
   (:require [angelic.util :as util] [angelic.old  [envs :as envs]]              
	     ))


;;; An auxillary data structure to hold cached features of env, heuristics.

(defstruct state-space-search-space-struct :class :state-space :action-space :goal :lower-reward-fn :upper-reward-fn :env #_:enforce-consistency?)

(defn make-state-space-search-space- [state-space action-space goal lower-reward-fn upper-reward-fn env #_ enforce-consistency?]
;  (util/assert-is (contains? #{true false :warn} enforce-consistency?))
 ; (util/assert-is (contains? #{false} enforce-consistency?))
  (struct state-space-search-space-struct ::StateSpaceSearchSpace state-space action-space goal lower-reward-fn upper-reward-fn env #_ enforce-consistency?))



;;; Main node data structure

(derive ::StateSpaceNode ::angelic.old.search/Node)

(defstruct state-space-node :class :search-space :state)

(defn make-state-space-node [search-space state #_ path-min]
 ; (with-meta 
   (struct state-space-node ::StateSpaceNode search-space state))
;   {:path-min path-min}))


;;; Only methods to call here is:

(defn state-space-search-space
  ([env] 
     (state-space-search-space env (constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (state-space-search-space env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
;  ([env lower-reward-fn upper-reward-fn]
;     (state-space-search-space env lower-reward-fn upper-reward-fn true))
  ([env lower-reward-fn upper-reward-fn #_ enforce-consistency?]
     (make-state-space-search-space- (envs/get-state-space env) (envs/get-action-space env) (envs/get-goal env) lower-reward-fn upper-reward-fn env #_ enforce-consistency?)))

(defn make-initial-state-space-node 
  ([env] 
     (make-initial-state-space-node env (constantly 0)));(constantly Double/POSITIVE_INFINITY)))
  ([env upper-reward-fn] 
     (make-initial-state-space-node env (constantly Double/NEGATIVE_INFINITY) upper-reward-fn))
;  ([env lower-reward-fn upper-reward-fn]
;     (make-initial-state-space-node env lower-reward-fn upper-reward-fn false))
  ([env lower-reward-fn upper-reward-fn #_enforce-consistency?]
     (make-state-space-node 
      (make-state-space-search-space- (envs/get-state-space env) (envs/get-action-space env) (envs/get-goal env) lower-reward-fn upper-reward-fn env #_enforce-consistency?)
      (envs/get-initial-state env)
      #_ Double/POSITIVE_INFINITY)))  

(defn ss-node [& args] (apply make-initial-state-space-node args))

;;; Node methods 

(defmethod node-environment   ::StateSpaceNode [node] (:env (:search-space node)))
(defmethod node-state         ::StateSpaceNode [node] (:state node))

(defmethod lower-reward-bound ::StateSpaceNode [node] 
  (+ (:reward (meta (:state node))) ((:lower-reward-fn (:search-space node)) (:state node))))

(defmethod upper-reward-bound ::StateSpaceNode [node] 
  (+ (:reward (meta (:state node))) ((:upper-reward-fn (:search-space node)) (:state node))))
;  (let [rew (+ (:reward (meta (:state node))) ((:upper-reward-fn (:search-space node)) (:state node)))
;	path-min (util/safe-get (meta node) :path-min)
;	consistency (util/safe-get-in node [:search-space :enforce-consistency?])]
;    (if consistency 
;      (if (< path-min rew)
;	  (do (when (= :warn consistency) (println "Warning: heuristic is inconsistent!"))
;	      path-min)
;	rew)
 ;     rew)))

(defmethod reward-so-far ::StateSpaceNode [node] 
  (:reward (meta (:state node))))

(defmethod immediate-refinements ::StateSpaceNode [node] 
  (util/timeout)
  (util/sref-up! *ref-counter* inc)
  (let [search-space (:search-space node)
	state (:state node)]
    (for [succ (envs/successor-states state (:action-space search-space))]
      (do (util/sref-up! *plan-counter* inc)
	  (make-state-space-node search-space succ)))))
;    (map #(make-state-space-node search-space % #_ (min (util/safe-get (meta node) :path-min) (upper-reward-bound node))) 
;	 )))

(defmethod primitive-refinement ::StateSpaceNode [node] 
  nil)

(defmethod extract-optimal-solution ::StateSpaceNode [node] 
  (and (= (upper-reward-bound node)
	  (reward-so-far node))
       (extract-a-solution node)))

(defmethod extract-a-solution ::StateSpaceNode [node]
  (when (envs/satisfies-condition? (:state node) (:goal (:search-space node)))
    [(:act-seq (meta (:state node))) (:reward (meta (:state node)))]))

(defmethod node-str ::StateSpaceNode [node] 
;  (envs/state-str (:state-space (:search-space node)) (:state node)))
;  (envs/state-str (:state-space (:search-space node)) (:state node)))
  (str (vec (map :name (:act-seq (meta (:state node)))))))


;(defmethod node-parent ::StateSpaceNode [node] 
;  Not implemented

(defmethod node-depth ::StateSpaceNode [node] 
  (count (:act-seq (meta (:state node)))))

(defmethod node-first-action ::StateSpaceNode [node]
  (nth (:act-seq (meta (:state node))) 0))




(comment
(take 5 (distinct (primitive-refinements-priority 
(search-problem->state-space-node
  (make-search-problem 
   (list 5)
   (let [act-inc (envs/make-action 'inc #(vector (list (inc (first %))) -1))
	 act-dec (envs/make-action 'dec #(vector (list (dec (first %))) -1))] 
     (envs/make-action-space 
      (fn [state]
	(cond (= (first state) 10) [act-dec]
	      (= (first state) 0)  [act-inc]
	      true                 [act-inc act-dec]))))
   (make-goal #(zero? (first %))))
  (constantly Double/NEGATIVE_INFINITY)
  (constantly 0)))))
   ) 










