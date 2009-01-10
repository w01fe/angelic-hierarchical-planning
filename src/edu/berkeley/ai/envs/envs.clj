(in-ns 'edu.berkeley.ai.envs)

(defmulti #^{:doc "Get metafied initial state"}   get-initial-state :class)
(defmulti #^{:doc "Get instance of state-space"}  get-state-space   :class)
(defmulti #^{:doc "Get instance of action-space"} get-action-space  :class)
(defmulti #^{:doc "Get instance of goal struct"}  get-goal          :class)

(defn metafy-initial-state [s]
  (with-meta s {:act-seq [] :reward 0}))


; Default, simple structure implementation

(defstruct environment :class :state-space :action-space :initial-state :goal)

(defn make-environment [initial-state state-space action-space goal]
  (struct environment ::Environment state-space action-space initial-state goal))

    
(defmethod get-initial-state ::Environment [env]
  (metafy-initial-state (:initial-state env)))

(defmethod get-state-space   ::Environment [env]
  (:state-space env))
  
(defmethod get-action-space  ::Environment [env]
  (:action-space env)) 

(defmethod get-goal          ::Environment [env]
  (:goal env))
  

