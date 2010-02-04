(ns exp.sas-flat
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util [queues :as queues]]
            [exp [env :as env]])
  (:import [java.util LinkedList HashMap HashSet ArrayList])
  )

;; This is an old version that tries to be efficient using numbered vars and vals.
;; It's about twice as fast as the simpler, more maintainable version in sas.clj.

(deftype SAS-Var     [num name n-vals val-names])

(deftype SAS-Action  [name preconditions effects cost]
  env/Action 
    (primitive?   [] true)
    (action-name  [] name)
  env/PrimitiveAction 
    (applicable?  [s]
      (every? (fn [[var val]] (= (nth s var) val)) preconditions))
    (next-state-and-reward [s]
      [(loop [s (transient s) e (seq effects)]
         (if-let [[[var val] & rest] e]
            (recur (assoc! s var val) rest)
          (persistent! s)))
       (- cost)]))

;; SAS-Problem will always have a special action goal-action-name and var goal-action-name with init 0, desired 1. 
(deftype SAS-Problem [vars init actions actions-fn]
  env/Env
    (initial-state [] init)
    (actions-fn    [] actions-fn)
    (goal-fn       [] #(= 1 (peek %)))
  env/FactoredEnv 
    (goal-map      [] {(dec (count vars)) 1}))

(defn make-simple-successor-generator [vars actions]
;  (println (count vars) (count actions))
  (cond (empty? vars)    (constantly actions)
        (empty? actions) (constantly nil)
        :else            
          (let [var-num (int (:num (first vars)))
                actions-by-val 
                  (util/group-by 
                   (fn [a] (second (first (filter #(= (first %) var-num) (:preconditions a)))))
                   actions)]
            (if (= (count actions-by-val) 1)
                (if (nil? (key (first actions-by-val)))
                    (make-simple-successor-generator (next vars) actions)
                  (let [v  (key (first actions-by-val))
                        sg (make-simple-successor-generator (next vars) actions)]
                    (fn successor-gen2 [s] (when (= v (nth s var-num)) (sg s)))))
              (let [dc-sg   (make-simple-successor-generator (next vars) (get actions-by-val nil)) 
                    val-sgs (vec (for [i (range (:n-vals (first vars)))]
                                   (make-simple-successor-generator (next vars) (get actions-by-val i))))]
                (fn successor-gen [s] (concat (dc-sg s) ((nth val-sgs (nth s var-num)) s))))))))

(defn make-sas-problem [vars init actions]
  (SAS-Problem vars init actions (make-simple-successor-generator vars actions)))


(def *working-dir* "/tmp/")
(def *lama-dir* "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/")

(defn lama-translate [stem]
  (util/sh (str *lama-dir* "translate/translate.py") (str stem "-domain.pddl") (str stem ".pddl")
           :dir *working-dir*))


(defn map-ize [key-fn s]
  (into {}
    (loop [s s, result nil]
      (if (empty? s) result
        (let [[k & r] s
              [vs r]  (split-with (complement key-fn) r)]
;          (println vs)
          (assert (key-fn k))
          (recur r (cons [ (key-fn k) vs] result)))))))

(defn read-groups-file
  "Read a groups file from LAMA and output a map from variable names to atoms."
  [file]
  (util/map-vals 
   (fn [vl] (map #(vec (map keyword (drop 2 (remove empty? (.split #^String % "[,() ]"))))) vl))
   (map-ize #(when-not (.startsWith #^String % " ") 
               (keyword (.substring #^String % 0 (dec (count %)))))
            (.split #^String (slurp file) "\n"))))



(defn make-sas-problem-from-pddl [stem]
;  (lama-translate stem)
  (println (lama-translate stem))
  (let [var-map (assoc (read-groups-file (str *working-dir* "test.groups"))
                  :goal ["no-goal" "goal"])
        sas-q   (LinkedList. (seq (.split #^String (slurp (str *working-dir* "output.sas"))
                                          "\n")))
        _       (dotimes [_ 3] (.pop sas-q))
        _       (assert (= (.pop sas-q) "begin_variables"))
        n-vars  (read-string (.pop sas-q))
        vars-ds (doall (for [_ (range n-vars) 
                             :let [[v ds] (.split #^String (.pop sas-q) " ")]]
                         (do (assert (not (= v "goal")))
                             [(keyword v) (read-string ds)])))
        _       (assert (= (.pop sas-q) "end_variables"))        
        _       (assert (= (.pop sas-q) "begin_state"))
        init-v  (vec (for [_ (range n-vars)] (read-string (.pop sas-q))))
        _       (assert (= (.pop sas-q) "end_state"))        
        _       (assert (= (.pop sas-q) "begin_goal"))
        goal-m  (into {} (for [_ (range (read-string (.pop sas-q)))]
                           (read-string (str "[" (.pop sas-q) "]"))))
        _       (assert (= (.pop sas-q) "end_goal"))
        ops     (doall (for [_ (range (read-string (.pop sas-q)))]
                         (let [_        (assert (= (.pop sas-q) "begin_operator")) 
                               name     (vec (map keyword (.split #^String (.pop sas-q) " ")))
                               prevails (doall (for [_ (range (read-string (.pop sas-q)))]
                                                 (read-string (str "[" (.pop sas-q) "]"))))
                               effects  (doall (for [_ (range (read-string (.pop sas-q)))]
                                                 (read-string (str "[" (.pop sas-q) "]"))))                              
                               cost     (read-string (.pop sas-q))]
                           (assert (not (= (first name) :goal)))
                           (assert (= (.pop sas-q) "end_operator"))
                           (assert (seq effects))
                           (assert (apply distinct? (concat (map first prevails)
                                                            (map #(nth % 1) effects))))
                           (assert (every? #(= 0 (first %)) effects))
;                           (assert (> cost 0))
                           (SAS-Action 
                            name
                            (concat (for [[_ v ov] effects :when (not (= ov -1))] [v ov]) 
                                    prevails)
                            (for [[_ v _ nv] effects] [v nv])
                            (if (= cost 0) 1 cost)))))]
    (make-sas-problem
     (vec (for [[i [n ds]] (util/indexed (concat vars-ds [[:goal 2]]))]
            (let [var-info (util/safe-get var-map n)]
              (SAS-Var i n ds (vec var-info)))))
     (conj init-v 0)
     (conj (vec ops) (SAS-Action goal-action-name (vec (map vec goal-m)) [[n-vars 1]] 0)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Simplification stuff ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn remapping [n-vals dead-vals merged-vals]
  (let [l (ArrayList. (range n-vals))
        merged-vals (sort merged-vals)]
    (doseq [v (sort dead-vals)]   (.add l v nil))
    (doseq [v (rest merged-vals)] (.add l v (first merged-vals)))
    (into {} (map vector (range n-vals) (seq l)))))

(defn remove-indices [v index-set]
  (vec (if (empty? index-set) v
           (map second (remove #(index-set (first %)) (util/indexed v))))))

(defn merge-vals
  ([x] x)
  ([x y] (cons ::or (map #(if (= (first %) ::or) (next %) [%]) [x y])))
  ([x y & more] (reduce merge-vals x (cons y more))))

;; Idea is: multiple untested vals per var can be merged, unset vals can be removed.
;;          Then, any var with 1 val can be removed entirely.
(defn renumber-sas-problem [vars actions init untested-vals unset-vals dead-actions]
  (let [rest-actions     (remove (set dead-actions) actions)
        unset-vals-v     (util/map-vals #(set (map second %)) (util/group-by first unset-vals))
        untst-vals-v     (util/map-vals #(set (map second %)) (util/group-by first untested-vals))        
        val-mappings     (vec (for [v vars] (remapping (:n-vals v) (unset-vals-v (:num v)) 
                                                                   (untst-vals-v (:num v)))))
        val-counts       (vec (map #(count (distinct (remove nil? (vals %)))) val-mappings))
        dead-vars        (set (for [[i c] (util/indexed val-counts)
                                    :when (< c 2)]
                                (do (assert (= c 1))
                                    (assert ((val-mappings i) (init i)))
                                    i)))
        var-mapping      (remapping (count vars) dead-vars nil)
        final-vars       (vec (for [var vars 
                                    :when (not (dead-vars (:num var)))
                                    :let  [val-mapping (val-mappings (:num var))]]
                                (SAS-Var (var-mapping (:num var)) (:name var) (val-counts (:num var))
                                         (vec (map #(apply merge-vals (second %))
                                                (sort-by first 
                                                  (util/group-by first
                                                    (for [[i v] (util/indexed (:val-names var))]
                                                      [(val-mapping i) v]))))))))
        final-actions    (vec (for [a rest-actions
                                    :let [fp (doall (for [[var-num val-num] (:preconditions a)
                                                           :let [new-var-num (var-mapping var-num)
                                                                 new-val-num (util/make-safe ((val-mappings var-num) 
                                                                                              val-num))]
                                                           :when new-var-num]
                                                       [new-var-num new-val-num]))
                                          fe (for [[var-num val-num] (:effects a)
                                                   :let [new-var-num (var-mapping var-num)
                                                         new-val-num ((val-mappings var-num) val-num)]
                                                   :when (and new-var-num new-val-num)]
                                               [new-var-num new-val-num])]
                                    :when (seq fe)]
                                (SAS-Action (:name a) (vec fp) (vec fe) (:cost a))))]
;    (println val-mappings "\n\n" var-mapping)
    (println "Removing"   (- (count actions) (count final-actions)) "actions," 
                            (count dead-actions) "initial;" 
                          (count dead-vars) "vars;"
                          (- (apply + (map :n-vals vars))
                             (apply + (map :n-vals final-vars))
                             (apply + (map #(:n-vals (vars %)) dead-vars))) "additional vals.")
    (make-sas-problem
     final-vars
     (remove-indices (map #(%1 %2) val-mappings init) dead-vars)
     final-actions)))

;; Can remove anything not referenced in a precondition except goal, unreachable values, etc.
;; NO. setting a variable can negate a precondition, making things worse. 
;; Latter seems done already by lama preprocesor, perhaps former too.
(defn forward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        untested-vals               (HashSet.)
        unset-vals                  (HashSet.)
        live-actions                (ArrayList.)
        action-precond-counts       (HashMap.)
        actions-by-precond          (HashMap.)
        stack                       (queues/make-stack-pq)]
    (doseq [var (butlast vars), val (range (:n-vals var))] 
      (.add untested-vals [(:num var) val])
      (.add unset-vals [(:num var) val]))
    (doseq [[var val] (util/indexed init)] (.remove unset-vals [var val]))
    (doseq [a actions]
      (.put action-precond-counts a (count (:preconditions a)))
      (when (empty? (:preconditions a)) (queues/pq-add! stack a 0))
      (doseq [e (:effects a)] (.remove unset-vals e))
      (doseq [p (:preconditions a)]
        (.remove untested-vals p)
        (.put actions-by-precond p (cons a (.get actions-by-precond p)))))
    (queues/pq-add! stack (SAS-Action [:init] []  (map vector (iterate inc 0) init) 0) 0)
    (while (not (queues/pq-empty? stack))
        (doseq [e (:effects (queues/pq-remove-min! stack))
                a (.remove actions-by-precond e)]
          (let [c (dec (.remove action-precond-counts a))]
            (if (> c 0)
                (.put action-precond-counts a c)
              (queues/pq-add! stack a 0)))))
;    (println (concat dead-vals (keys actions-by-precond)))
;    (println "DEAD ACTION PRECONDS: " (keys actions-by-precond))
    (println (util/map-vals count (util/group-by first  untested-vals)))
    (println (count unset-vals) (count untested-vals) (count actions-by-precond) (count action-precond-counts))
    (renumber-sas-problem vars actions init untested-vals (concat unset-vals (keys actions-by-precond)) 
                          (keys action-precond-counts))))

;; Can remove anything provably not on a shortest path to goal.  
;; Basically, this comes down to finding irrelevant "spokes" in DTGs and removing them. 
(defn backward-simplify [sas-problem]
  (let [{:keys [vars actions init]} sas-problem
        dead-vals                   (HashSet.)
        action-precond-counts       (HashMap.)
        actions-by-precond          (HashMap.)
        stack                       (queues/make-stack-pq)]
    (doseq [var (butlast vars), val (range (:n-vals var))] (.add dead-vals [(:num var) val]))
    (doseq [a actions]
      (.put action-precond-counts a (count (:preconditions a)))
      (when (empty? (:preconditions a)) (queues/pq-add! stack a 0))
      (doseq [p (:preconditions a)]
        (.remove dead-vals p)
        (.put actions-by-precond p (cons a (.get actions-by-precond p)))))
    (queues/pq-add! stack (SAS-Action [:init] []  (map vector (iterate inc 0) init) 0) 0)
    (while (not (queues/pq-empty? stack))
        (doseq [e (:effects (queues/pq-remove-min! stack))
                a (.remove actions-by-precond e)]
          (let [c (dec (.remove action-precond-counts a))]
            (if (> c 0)
                (.put action-precond-counts a c)
              (queues/pq-add! stack a 0)))))
    (println (count dead-vals) (count actions-by-precond) (count action-precond-counts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Causal graph stuff ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn compute-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (for [action actions
           precondition (concat (:preconditions action) (:effects action))
           effect       (:effects action)]
       [(first precondition) (first effect)]))))

(defn compute-relaxed-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (distinct
     (concat (for [i (range (count vars))] [i i])
             (for [action actions
                   precondition (:preconditions action)
                   effect       (:effects action)]
               [(first precondition) (first effect)])))))


(defn cnum [[x y]] (+ (* x 10000) y))
(defn compute-full-causal-graph [sas-problem]
  (let [vars    (:vars sas-problem)
        actions (:actions sas-problem)]
    (apply concat 
           (for [[i action] (util/indexed actions)]
             (concat (for [precondition (:preconditions action)] [(cnum precondition) (- -1 i)])
                     (for [effect       (:effects action)      ] [(- -1 i) (cnum effect)]))))))