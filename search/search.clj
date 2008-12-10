(ns search
 (:refer-clojure)
 )


(defn make-boolean-state-space [vars] 
  {:class ::BooleanStateSpace :vars vars})

(derive ::BooleanStateSpace ::StateSpace)


(defn make-boolean-state [space val-map] 
  (assoc val-map :class ::BooleanState :state-space space))

(derive ::BooleanState ::State)


;(defn make-state-set 

(defmulti enumerate-states :class)

(declare enumerate-boolean-maps)

(defn enumerate-boolean-maps [vars]
  (if (nil? vars)
    [{}]
    (let [recs (enumerate-boolean-maps (rest vars))]
      (for [item '(true false) state recs] 
        (assoc state (first vars) item)))))

(defmethod enumerate-states ::BooleanStateSpace [space]
  (map #(make-state space %) (enumerate-boolean-maps (:vars space))))


(defn stupidpow [x n]
  (loop [ret 1.0 n n]
    (if (= n 0) ret (recur (* ret x) (- n 1)))))

(defn stupidpow2 [x n]
  (let [x (double x) n (int n)]
    (reduce * (take n (repeat x)))))

(defn mypow [x n]
  (let [x (double x)]
    (loop [ret (double 1.0) n (int n)]
      (if (== (int 0) n) ret (recur (* ret x) (unchecked-dec n))))))