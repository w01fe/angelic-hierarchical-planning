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
  

;; Useful sanity check




(defn check-solution [env [act-seq reward]]
  (let [action-space (get-action-space env)
	init         (get-initial-state env)
	goal         (get-goal env)
	action-map   (map-map #(vector (:name %) %) (all-actions action-space))]
    (loop [state init rest-act-seq act-seq]
      (if (seq rest-act-seq)
	  (let [next1 (safe-next-state state (first rest-act-seq))
		next2 (safe-next-state state (safe-get action-map (:name (first rest-act-seq))))]
	    (assert-is (= next1 next2))
	    (assert-is (= (:reward ^next1) (:reward ^next2)))
	    (recur next1 (rest rest-act-seq)))
	(do 
	  (assert-is (satisfies-condition? state goal))
	  (assert-is (= reward (:reward ^state)))
	  [act-seq reward state])))))