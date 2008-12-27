(in-ns 'edu.berkeley.angel.search)

(defstruct search-problem :class :action-space :initial-state :goal)

(defn make-search-problem [initial-state action-space goal]
  (struct search-problem ::SearchProblem action-space initial-state goal))

(defn get-initial-state [search-problem]
  (with-meta 
   (:initial-state search-problem)
   {:act-seq [] :reward 0}))
  
(defn get-action-space [search-problem]
  (:action-space search-problem))

(defn get-goal [search-problem]
  (:goal search-problem))
  
