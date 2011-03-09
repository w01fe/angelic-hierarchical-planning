(ns angelic.old.envs
 (:require [angelic.util :as util] 
           [angelic.util [propositions :as props]])
 )

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

(defmulti #^{:doc "Get string rep of state"}      state-str (fn [env elt] (:class env)))

(defmethod state-str  ::Environment [env state] (state-str (get-state-space env) state))  


(derive ::SubEnvironment ::Environment)
(defstruct str-sub-environment :class :env :initial-state :goal)

; Can't do this because of goal preprocessing. .. 
(defn sub-environment "Make a new environment with changed initial state and/or goal.  This may be very DANGEROUS since instance may preprocess the goal in ways not taken into account here."
  ([env new-init] (sub-environment env new-init (get-goal env)))
  ([env new-init new-goal]
     (struct str-sub-environment ::SubEnvironment
	     (if (isa? (:class env) ::SubEnvironment) (util/safe-get env :env) env)
	     new-init new-goal)))

(defmethod get-state-space   ::SubEnvironment [env]
  (get-state-space (util/safe-get env :env)))
  
(defmethod get-action-space  ::SubEnvironment [env]
  (get-action-space (util/safe-get env :env)))


; For real-time algorithms.
(defn next-environment [[env [act-seq reward-so-far]] action]
  (let [state (get-initial-state env)
	[next reward] ((:fn action) state)]
    [(sub-environment env next  (get-goal env))
     [(conj act-seq action)
      (+ reward-so-far reward)]]))



;::PropositionalEnvironment

(derive ::PropositionalEnvironment ::Environment)

(defmulti #^{:doc "Get the ::PropositionalDomain associated with this ::PropositionalEnvironment"}
  get-domain :class)

(defmulti #^{:doc "Get the expected number of distinct values for arg-pos allowed by pred, given inst-pos vars instantiated."}
  expected-domain-size (fn [inst pred arg-pos inst-pos] (:class inst)))




;; Load containing files.

(doseq [f '[conditions states actions]]
   (load (str "envs/" f)))




;; Useful sanity check


(defn solution-name [[act-seq reward]]
  [(map :name act-seq) reward])

(defn check-solution [env [act-seq reward]]
  (let [action-space (get-action-space env)
	init         (get-initial-state env)
	goal         (get-goal env)
	action-map   (util/map-map #(vector (:name %) %) (all-actions action-space))]
    (loop [state init rest-act-seq act-seq state-seq [init]]
      (if (seq rest-act-seq)
	  (let [next1 (safe-next-state state (first rest-act-seq))
		next2 (safe-next-state state (util/safe-get action-map (:name (first rest-act-seq))))]
	    (util/assert-is (= next1 next2))
	    (util/assert-is (= (:reward (meta next1)) (:reward (meta next2))))
	    (recur next1 (next rest-act-seq) (conj state-seq next1)))
	(do 
	  (util/assert-is (satisfies-condition? state goal))
	  (util/assert-is (= reward (:reward (meta state))))
	  [act-seq reward state-seq])))))
