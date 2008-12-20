(in-ns 'edu.berkeley.angel.search)

;; action-fn returns set of actions given state
;; action returns [result cost] pair

(defstruct search-space :class :state-space :action-space :action-fn)

(defn make-search-space [state-space action-space action-fn]
  (struct search-space ::SearchSpace state-space action-space action-fn))


(defstruct search-problem :class :search-space :initial-state :goal-test)

(defn make-search-problem [search-space initial-state goal-test]
  (struct search-problem ::SearchProblem search-space initial-state goal-test))

(defn successors [state action-fn]
  "Return a lazy seq of (action successor cost) seqs"
  (map #(cons (:name %) (apply-action state %)) (action-fn state)))

(defn successor-states [state action-fn]
  "Return a lazy seq of successor states"
  (map #(first (apply-action state %)) (action-fn state)))


