(in-ns 'edu.berkeley.angel.envs)


(defstruct action :class :name :fn)

(defn make-action "function is a fn from states to [state reward] pairs.  "
  [name next-fn]
  (struct action ::Action name next-fn))

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


(defmulti applicable-actions #(vector (:class %1) (:class %2)))

       
(defstruct action-space :class :fn)

(defn make-action-space "function is a map from states to lazy seq of action objects"
  [fn]
  (struct action-space ::ActionSpace fn))
 
(defmethod applicable-actions :default [state action-space]
  ((:fn action-space) state))
 
  
(defn successor-states [state action-space]
  (map #(next-state state %) (applicable-actions state action-space)))
  




