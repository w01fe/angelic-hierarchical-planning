; Textbook algorithms for fully observable, deterministic problems
; with countable state spaces and finite action spaces.

(ns edu.berkeley.ai.search.algorithms.real-time
  (:refer-clojure)
  (:use (edu.berkeley.ai [util :as util] envs search))
  )


(def *debug-level* 0)

(defn real-time-search "Generic real-time search.  Action-fn maps node->primitive"
  [state state->search-node max-steps action-fn]
  (loop [[state cur-seq] [state [[] 0]], max-steps max-steps]
;  (when (> *debug-level* 0) (prn (clojure.set/intersection state #{'(on d c) '(on c b) '(on b a)})))
    (let [node (state->search-node state)]
      (when (> *debug-level* 0) (prn) (prln (node-str node)))
      (or (and (extract-optimal-solution node) cur-seq)
	  (and (> max-steps 0) 
	       (recur 
		(next-initial-state
		 [state cur-seq]
		 (action-fn node state))
		(dec max-steps)))))))

; TODO: Various versions for search strategies, alpha pruning, etc.
(defn lookahead-search "Standard depth-limited greed loookahead search"
  [state state->search-node max-steps search-depth]
  (real-time-search state state->search-node max-steps
    (fn [node state] 
      (node-first-action 
       (random-maximal-element upper-reward-bound (refinements-depth node search-depth))))))


(import '(java.util HashMap))

; TODO: Various versions for search strategies, alpha pruning, etc.
(defn lrta-star "Korf's classic LRTA* with a fixed depth limit. Only for state-space search."
  [env upper-reward-fn max-steps search-depth]
  (let [space (state-space-search-space env upper-reward-fn)
	#^HashMap m (HashMap.)]
    (real-time-search 
     (get-initial-state env)
     (partial make-state-space-node space)
     max-steps
     (fn [node state]
       (let [nodes (map-leaf-refinements-depth 
		     node
		     #(when-let [r (and (not= node %) (.get m (:state %)))]
;			(prn ". " (:state %) r (reward-so-far %) (upper-reward-bound (adjust-reward % (+ r (reward-so-far %)))))
			(adjust-reward % (+ r (reward-so-far %))))
		     search-depth)
	     best (random-maximal-element upper-reward-bound nodes)]
	 (.put m state (upper-reward-bound best))
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
      (get-initial-state instance)
      (partial make-state-space-node space)
      100 1))) nil))

; greedy lookahead - # of conjuncts
(let [instance 
	(read-strips-planning-instance
	 (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
	 "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
	    space (state-space-search-space instance #(- (count (clojure.set/difference (set (:goal-atoms instance)) %))))]
	(frequencies (map #(when % true) (take 1000 (repeatedly (fn []
     (lookahead-search 
      (get-initial-state instance)
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
      #(- (count (clojure.set/difference (set (:goal-atoms instance)) %)))
      1000
      1)))))))




      

		       
;      (state-space-search-node  
     
;     #(- (count (clojure.set/intersection )
;     )))




   
     
)



	
  
