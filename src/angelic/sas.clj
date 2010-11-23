(ns angelic.sas
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util])
  (:import [java.util LinkedList])
  )


(defrecord SAS-Var [name vals])
(defn make-sas-var [name vals] (SAS-Var. name vals))


;; SAS-Problem will always have a special action goal-action-name and var :goal with init [:goal :false], desired [:goal :true]. 

(def goal-action-name [:goal])
(def goal-var-name    [:goal :?])
(def goal-true-val    [:goal :true])
(def goal-false-val   [:goal :false])
(def goal-var (make-sas-var goal-var-name #{goal-true-val goal-false-val}))

(defrecord SAS-Problem [vars init actions actions-fn]
  env/Env
  (initial-state [_] init)
  (actions-fn    [_] (force actions-fn))
  (goal-fn       [_] #(= (util/safe-get % goal-var-name) goal-true-val))

  env/FactoredEnv 
  (goal-map      [_] {goal-var-name goal-true-val}))

(defn make-simple-successor-generator [var-names actions]
;  (println vars actions)
 ;  (println (count vars) (count actions))
  (cond (empty? var-names)    (constantly actions)
        (empty? actions) (constantly nil)
        :else            
        (let [[var-name & more-var-names] var-names
              actions-by-val    (group-by #((:precond-map %) var-name) actions)]
            (if (= (count actions-by-val) 1)
                (if (nil? (key (first actions-by-val)))
                    (make-simple-successor-generator more-var-names actions)
                  (let [v  (key (first actions-by-val))
                        sg (make-simple-successor-generator more-var-names actions)]
                    (fn successor-gen2 [s] (when (= v (state/get-var s var-name)) (sg s)))))
              (let [dc-sg   (make-simple-successor-generator more-var-names (get actions-by-val nil)) 
                    val-sgs (util/map-vals #(make-simple-successor-generator more-var-names %) actions-by-val)]
                (fn successor-gen [s] (concat (dc-sg s) (when-let [f (val-sgs (state/get-var s var-name))] (f s)))))))))

(defn make-sas-problem [vars init actions]
  (SAS-Problem. vars init actions (delay (make-simple-successor-generator (keys vars) actions))))


(def *working-dir* "/tmp/")
(def *lama-dir* "/Users/jawolfe/Projects/research/planners/seq-sat-lama/lama/")

(defn lama-translate 
  ([stem] (lama-translate (str stem "-domain.pddl") (str stem ".pddl")))
  ([domain-file inst-file]
     (let [ret #^String (util/sh (str *lama-dir* "translate/translate.py") 
                                 domain-file inst-file :dir *working-dir*)]
       (when-not (.endsWith ret "Done!\n")
         (throw (RuntimeException. (str "LAMA-translate failed: "  ret))))
       ret  )))


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
   (fn [vl] (map #(let [tokens (remove empty? (.split #^String % "[,() ]"))]
                    (if (= (second tokens) "Atom")
                        (do (assert (not (= (nth tokens 2) "other")))
                            (vec (map keyword (drop 2 tokens))))
                      [:other])) 
                 vl))
   (map-ize #(when-not (.startsWith #^String % " ") 
               (keyword (.substring #^String % 0 (dec (count %)))))
            (.split #^String (slurp file) "\n"))))

(defn expand-condition [vars [varn valn]]
  (let [var (nth vars varn)]
    [(:name var) (nth (:vals var) valn)]))

(defn infer-var-name [val-names]
  (let [by-f       (group-by first val-names)
        prototypes (for [props (vals by-f)]
                     (vec (for [elts (apply map vector props)]
                            (if (apply = elts) (first elts) :?))))]
    (if (= (count prototypes) 1) (first prototypes) (vec (cons :or prototypes)))))

;(defn infer-var-name [boring-name val-names]
;  (let [val-names (remove #(= [:other] %) val-names)
;        prototype (for [elts (apply map vector val-names)]
;                    (if (apply = elts) (first elts) :?))]
;    (if (= (first prototype) :?) boring-name (vec prototype))))

(defn make-sas-problem-from-pddl 
  ([stem] (make-sas-problem-from-pddl  (str stem "-domain.pddl") (str stem ".pddl")))
  ([domain-file inst-file]
     (let [lto  (lama-translate domain-file inst-file)]
       (util/print-debug 1 lto))
     (let [var-map (assoc (read-groups-file (str *working-dir* "test.groups"))
                     goal-var-name [goal-false-val goal-true-val])
           sas-q   (LinkedList. (seq (.split #^String (slurp (str *working-dir* "output.sas")) "\n")))
           _       (dotimes [_ 3] (.pop sas-q))
           _       (assert (= (.pop sas-q) "begin_variables"))
           n-vars  (read-string (.pop sas-q))
           vars-ds (doall (for [_ (range n-vars) 
                                :let [[v ds] (.split #^String (.pop sas-q) " ")]]
                            (do (assert (not (= v "goal")))
                                [(keyword v) (read-string ds)])))
           _       (assert (= (.pop sas-q) "end_variables"))
           vars    (vec (for [[i [n ds]] (util/indexed (concat vars-ds [[goal-var-name 2]]))]
                          (let [var-info (util/safe-get var-map n)]
                            (SAS-Var. (infer-var-name var-info) (vec var-info)))))
           _       (util/assert-is (apply distinct? (map :name vars)))
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
                              (util/assert-is (every? #(= 0 (first %)) effects))
                              (env-util/make-factored-primitive 
                               name
                               (into {} (map (partial expand-condition vars)
                                             (concat (for [[_ v ov] effects :when (not (= ov -1))] [v ov]) 
                                                     prevails)))
                               (into {} (map (partial expand-condition vars) (for [[_ v _ nv] effects] [v nv])))
                               (if (= cost 0) -1 (- cost))))))]
       (make-sas-problem 
        (into {} (map (juxt :name identity) vars)) 
        (util/map-map (partial expand-condition vars) (util/indexed (conj init-v 0)))
        (conj (vec ops) 
              (env-util/make-factored-primitive goal-action-name (util/map-map (partial expand-condition vars) goal-m) 
                                     {goal-var-name goal-true-val} 0))))))






