(in-ns 'edu.berkeley.ai.envs)


(defstruct action :class :name :fn :precondition)

(defn make-action "function is a fn from states to [state reward] pairs.  "
  [name next-fn precondition]
  (struct action ::Action name next-fn precondition))



(def *next-counter* (util/sref 0))

(defn reset-next-counter [] 
  (util/sref-set! *next-counter* 0))

(defn next-state [state action]
;  (prn "next?" (:name action))
  (util/sref-set! *next-counter* (inc (util/sref-get *next-counter*)))
  (let [[next reward] ((:fn action) state)]
    (with-meta next
      {:act-seq (conj (:act-seq ^state) action)
       :reward (+ reward (:reward ^state))})))

(defn next-state-and-reward [state action]
;  (prn "next" (:name action))
  (util/sref-set! *next-counter* (inc (util/sref-get *next-counter*)))
  (let [[next reward] ((:fn action) state)]
    [(with-meta next
       {:act-seq (conj (:act-seq ^state) action)
        :reward (+ reward (:reward ^state))})
     reward]))

(defn next-initial-state [[state [act-seq reward-so-far]] action]
  (aset *next-counter* 0 (inc (aget *next-counter* 0)))
  (let [[next reward] ((:fn action) state)]
    [(with-meta next ^state)
     [(conj act-seq action)
      (+ reward-so-far reward)]]))


(defn legal-action? [state action]
;  (prn state action)
  (satisfies-condition? state (:precondition action)))

(defn safe-next-state [state action]
  (util/assert-is (legal-action? state action))
  (next-state state action))

(defn apply-actions [state actions]
  (reduce next-state state actions))

(defn safe-apply-actions [state actions]
  (reduce safe-next-state state actions))




;; TODO: implicit sets

(defmulti applicable-actions (fn [state action-space] (:class action-space)))
(defmulti all-actions :class)

       
(defstruct enumerated-action-space :class :fn :all-actions)

(defn make-enumerated-action-space "if provided, function is a map from states to lazy seq of action objects"
  ([acts] (make-enumerated-action-space acts (fn [x] (filter #(legal-action? x %) acts))))
  ([acts fn] (struct enumerated-action-space ::EnumeratedActionSpace fn acts)))

(defmethod applicable-actions ::EnumeratedActionSpace [state action-space]
  ((:fn action-space) state))

(defmethod all-actions ::EnumeratedActionSpace [action-space]
  (:all-actions action-space))
   
(defn successor-states [state action-space]
;  (prn state action-space)
  (map #(next-state state %) (applicable-actions state action-space)))
  
