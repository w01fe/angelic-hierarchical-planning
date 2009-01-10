(in-ns 'edu.berkeley.ai.envs)


(defstruct action :class :name :fn :precondition)

(defn make-action "function is a fn from states to [state reward] pairs.  "
  [name next-fn precondition]
  (struct action ::Action name next-fn precondition))



;(def *next-counter* (make-array Integer/TYPE 1))

;(defn reset-next-counter [] 
;  (aset *next-counter* 0 0))

(defn next-state [state action]
;  (aset *next-counter* 0 (inc (aget *next-counter* 0)))
  (let [[next reward] ((:fn action) state)]
    (with-meta next
      {:act-seq (conj (:act-seq ^state) action)
       :reward (+ reward (:reward ^state))})))

(defn next-initial-state [[state [act-seq reward-so-far]] action]
;  (aset *next-counter* 0 (inc (aget *next-counter* 0)))
  (let [[next reward] ((:fn action) state)]
    [(with-meta next ^state)
     [(conj act-seq action)
      (+ reward-so-far reward)]]))


(defn legal-action? [state action]
  (satisfies-condition? state (:precondition action)))

(defn safe-next-state [state action]
  (assert-is (legal-action? state action))
  (next-state state action))

(defn apply-actions [state actions]
  (reduce next-state state actions))

(defn safe-apply-actions [state actions]
  (reduce safe-next-state state actions))




;; TODO: implicit sets

(defmulti applicable-actions #(vector (:class %1) (:class %2)))
(defmulti all-actions :class)

       
(defstruct enumerated-action-space :class :fn :all-actions)

(defn make-enumerated-action-space "if provided, function is a map from states to lazy seq of action objects"
  ([acts] (make-enumerated-action-space acts #(filter (partial legal-action? %) acts)))
  ([acts fn] (struct enumerated-action-space ::EnumeratedActionSpace fn acts)))

(defmethod applicable-actions ::EnumeratedActionSpace [state action-space]
  ((:fn action-space) state))

(defmethod all-actions ::EnumeratedActionSpace [action-space]
  (:all-actions action-space))
   
(defn successor-states [state action-space]
  (map #(next-state state %) (applicable-actions state action-space)))



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
