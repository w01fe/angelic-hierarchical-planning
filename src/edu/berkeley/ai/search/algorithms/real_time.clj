(ns edu.berkeley.ai.search.algorithms.real-time
  (:refer-clojure)
  (:use [edu.berkeley.ai.search :as search])
  (:require [edu.berkeley.ai [util :as util] [envs :as envs]])
  )
;;; Textbook algorithms for fully observable, deterministic problems
;;; with countable state spaces and finite action spaces.

; TODO: fix these up ...

(def *debug-level* 0)

(defn real-time-search "Generic real-time search.  Action-fn maps node->primitive"
  [env max-steps action-fn]
  (let [goal (envs/get-goal env)]
    (loop [[env cur-seq] [env [[] 0]], max-steps max-steps]
      (if (envs/satisfies-condition? (envs/get-initial-state env) goal)
	  cur-seq
        (let [state (envs/get-initial-state env)]
	  (when (> *debug-level* 0) (prn) (util/prln (envs/state-str env state)))
	  (when (> max-steps 0) 
	    (recur 
	     (envs/next-environment
	      [env cur-seq]
	      (action-fn env))
	     (dec max-steps))))))))

; TODO: Various versions for search strategies, alpha pruning, etc.
(defn lookahead-search "Standard depth-limited greed loookahead search"
  [env env->search-node max-steps search-depth]
  (real-time-search env max-steps
    (fn [env] 
      (node-first-action 
       (util/random-maximal-element upper-reward-bound 
	 (refinements-depth (env->search-node env) search-depth))))))


(import '(java.util HashMap))

; TODO: Various versions for search strategies, alpha pruning, etc.
(defn lrta-star "Korf's classic LRTA* with a fixed depth limit. Only for state-space search."
  [env upper-reward-fn max-steps search-depth]
  (let [#^HashMap m (HashMap.)]
    (real-time-search 
     env 
     max-steps
     (fn [env]
       (let [node (ss-node env)
	     nodes (map-leaf-refinements-depth 
		     node
		     #(when-let [r (and (not= node %) (.get m (:state %)))]
;			(prn ". " (:state %) r (reward-so-far %) (upper-reward-bound (adjust-reward % (+ r (reward-so-far %)))))
			(adjust-reward % (+ r (reward-so-far %))))
		     search-depth)
	     best (util/random-maximal-element upper-reward-bound nodes)]
	 (.put m (envs/get-initial-state (node-environment env)) (upper-reward-bound best))
;	 (prn (or (:state best) (cons "O" (:state (:node best)))) (upper-reward-bound best))
	 (node-first-action best))))))

   






(comment
; uninformed lookahead
(second (or (let [instance 
	(read-strips-planning-instance
	 (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
	 "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
	space (state-space-search-space instance (constantly 0))]
    (time 
     (lookahead-search 
      (envs/get-initial-state instance)
      (partial make-state-space-node space)
      100 1))) nil))

; greedy lookahead - # of conjuncts
(let [instance 
	(read-strips-planning-instance
	 (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
	 "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
	    space (state-space-search-space instance #(- (count (util/difference (util/to-set (:goal-atoms instance)) %))))]
	(frequencies (map #(when % true) (take 1000 (repeatedly (fn []
     (lookahead-search 
      (envs/get-initial-state instance)
      (partial make-state-space-node space)
      100 1)))))))


; lrta* - # of conjuncts
(let [instance 
	(read-strips-planning-instance
	 (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
	 "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")]
  (frequencies (map #(when % true) (take 100 (repeatedly (fn []
     (lrta-star
      instance
      #(- (count (util/difference (set (:goal-atoms instance)) %)))
      1000
      1)))))))




      

		       
;      (state-space-search-node  
     
;     #(- (count (util/intersection )
;     )))




   
     
)



	
  
