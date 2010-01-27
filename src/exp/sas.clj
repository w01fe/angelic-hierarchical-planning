(ns exp.sas
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env]])
  (:import [java.util LinkedList])
  )

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

;; SAS-Problem will always have a special action [:goal] and var [:goal] with init 0, desired 1. 
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
  (map-ize #(when-not (.startsWith #^String % " ") 
              (keyword (.substring #^String % 0 (dec (count %)))))
           (.split #^String (slurp file) "\n")))


(defn make-sas-problem-from-pddl [stem]
  (lama-translate stem)
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
                           (assert (> cost 0))
                           (SAS-Action 
                            name
                            (concat (for [[_ v ov] effects :when (not (= ov -1))] [v ov]) 
                                    prevails)
                            (for [[_ v _ nv] effects] [v nv])
                            cost))))]
    (make-sas-problem
     (vec (for [[i [n ds]] (util/indexed (concat vars-ds [[:goal 2]]))]
            (let [var-info (util/safe-get var-map n)]
              (SAS-Var i n ds (vec var-info)))))
     (conj init-v 0)
     (conj (vec ops) (SAS-Action [:goal] (vec (map vec goal-m)) [[n-vars 1]] 0)))))


