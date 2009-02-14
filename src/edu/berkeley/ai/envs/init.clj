(in-ns 'edu.berkeley.ai.envs)

(defmulti #^{:doc "Get string rep of state"}      state-str (fn [env elt] (:class env)))