(in-ns 'edu.berkeley.angel.search)

(defstruct search-problem :class :state-space :action-space :initial-state :goal)

(defn make-search-problem [initial-state state-space action-space goal]
  (struct search-problem ::SearchProblem state-space action-space initial-state goal))

(defn get-initial-state [search-problem]
  (with-meta 
   (:initial-state search-problem)
   {:act-seq [] :reward 0}))

(defn get-state-space [search-problem]
  (:state-space search-problem))
  
(defn get-action-space [search-problem]
  (:action-space search-problem))

(defn get-goal [search-problem]
  (:goal search-problem))
  
