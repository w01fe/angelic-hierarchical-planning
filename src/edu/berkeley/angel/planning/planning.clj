(in-ns 'edu.berkeley.angel.planning)


(defmulti #^{:doc "take a planning domain, a map from types to 
                   objects, a list of facts true in the initial state, 
                   and a goal specifyer, and return a planning problem instance."}
  instantiate-planning-domain #(:class %1))

(defmulti #^{:doc "take a planning problem instance and get a corresponding
                   state-space search problem."}
  planning-problem->state-space-search-problem :class)




