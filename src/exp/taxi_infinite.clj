(ns exp.taxi-infinite
  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [sas :as sas]])
  (:import [java.util Random]))



(defn- make-left   [s]
  (let [cx     (env/get-var s '[atx])]
    (when (> cx 1) 
      (env/FactoredPrimitive ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn- make-right  [s]
  (let [const (env/get-var s :const)
        width  (get const '[width])
        cx     (env/get-var s '[atx])]
    (when (< cx width)  
      (env/FactoredPrimitive ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn- make-down  [s]
  (let [cy     (env/get-var s '[aty])]
    (when (> cy 1)
      (env/FactoredPrimitive ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn- make-up    [s]
  (let [const (env/get-var s :const)
        height (get const '[height])
        cy     (env/get-var s '[aty])]
    (when (< cy height)
      (env/FactoredPrimitive ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn- make-pickup  [s pass [x y]]
  (env/FactoredPrimitive 
   ['pickup pass x y] 
   {['atx]        x     ['aty]        y
    ['passx pass] x     ['passy pass] y}
   {['passx pass] :taxi ['passy pass] :taxi}
   -1))

(defn- make-dropoff [s pass [x y]]
  (when pass 
    (env/FactoredPrimitive 
     ['dropoff pass x y] 
     {['atx]        x     '[aty] y 
      ['passx pass] :taxi ['passy pass] :taxi}
     {['passx pass] x     ['passy pass] y}
     -1)))


(deftype InfiniteTaxiEnv [width height passengers] :as this
 env/Env
  (initial-state []
    (into {:const {['width] width ['height] height}
           ['atx] 1 ['aty] 1}
          (apply concat
            (for [[name [sx sy]] passengers]
              [[['passx name] sx] [['passy name] sy]]))))
  (actions-fn []
   (fn taxi-actions [s]
     (filter identity
       (apply concat 
         (map #(% s) [make-left make-right make-up make-down])
         (for [[pass] passengers x (range 1 (inc width)) y (range 1 (inc height))] 
           [(make-pickup s pass [x y]) (make-dropoff s pass [x y])])))))
  (goal-fn [] 
    (let [goal-map (env/goal-map this)]
      #(when (env/state-matches-map? % goal-map)
         (env/solution-and-reward %))))
 env/FactoredEnv
  (goal-map [] 
    (into {} 
      (apply concat 
        (for [[pass _ [dx dy]] passengers] 
          [[['passx pass] dx] [['passy pass] dy]])))))


(defn make-random-infinite-taxi-env 
  ([width height n-passengers] 
     (make-random-infinite-taxi-env width height n-passengers (rand-int 10000000)))
  ([width height n-passengers seed]
     (let [r (Random. seed)]
       (.nextDouble r) (.nextDouble r)
       (InfiniteTaxiEnv width height
                (for [i (range n-passengers)]
                  [(symbol (str "pass" i))
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]])))))

(require 'exp.ucs)
(deftest infinite-taxi
  (is (= -15 (second (exp.ucs/uniform-cost-search (InfiniteTaxiEnv 5 5 [[:red [2 1] [5 4]] [:green [1 4] [3 3]]]))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical to above.

(defn- write-infinite-taxi-strips-domain [file]
  (util/spit file
    ";; Taxi domain 
     
     (define (domain infinite-taxi)
       (:requirements :typing)
       (:types x y pass)
       (:constants InTaxiX - x InTaxiY - y)
       (:predicates 
          (LEFTOF ?x1 ?x2 - x)
          (ABOVE  ?y1 ?y1 - y)
          (atx ?x - x)
          (aty ?y - y)
          (passx ?p - pass ?x - x)
          (passy ?p - pass ?y - y))
       
       (:action pickup 
         :parameters (?p - pass ?x - x ?y - y)
         :precondition (and (atx ?x)            (aty ?y)
                            (passx ?p ?x)       (passy ?p ?y))
         :effect       (and (not (passx ?p ?x)) (not (passy ?p ?y))
                            (passx ?p InTaxiX)  (passy ?p InTaxiY)))
                          
       (:action putdown 
         :parameters (?p - pass ?x - x ?y - y)
         :precondition (and (atx ?x)                  (aty ?y)
                            (passx ?p InTaxiX)        (passy ?p InTaxiY))
         :effect       (and (not (passx ?p InTaxiX))  (not (passy ?p InTaxiY))
                            (passx ?p ?x)             (passy ?p ?y)))
                          
       (:action left 
         :parameters (?l1 ?l2 - x)
         :precondition (and (atx ?l1) (LEFTOF ?l2 ?l1))
         :effect       (and (not (atx ?l1)) (atx ?l2)))

       (:action right 
         :parameters (?l1 ?l2 - x)
         :precondition (and (atx ?l1) (LEFTOF ?l1 ?l2))
         :effect       (and (not (atx ?l1)) (atx ?l2)))

       (:action up 
         :parameters (?l1 ?l2 - y)
         :precondition (and (aty ?l1) (ABOVE ?l2 ?l1))
         :effect       (and (not (aty ?l1)) (aty ?l2)))

       (:action down 
         :parameters (?l1 ?l2 - y)
         :precondition (and (aty ?l1) (ABOVE ?l1 ?l2))
         :effect       (and (not (aty ?l1)) (aty ?l2))))"
         
        ))

(defn- write-infinite-taxi-strips-instance [tenv file]
  (let [{:keys [width height passengers]} tenv]
    (util/spit file
      (util/str-join "\n"
        ["(define (problem infinite-taxi-)
           (:domain infinite-taxi)
           (:objects "
              (util/str-join " " (map first passengers)) " - pass"
              (util/str-join " " (map (partial str "x") (range 1 (inc width)))) " - x"
              (util/str-join " " (map (partial str "y") (range 1 (inc width)))) " - y"              
         "    )
           (:init "
              (util/str-join " " (for [x (range 1 width)] (str "(LEFTOF x" x " x" (inc x) ")")))
              (util/str-join " " (for [y (range 1 height)] (str "(ABOVE y"  (inc y) " y" y ")")))              
              "(atx x1)" "(aty y1)"
              (util/str-join " " (apply concat
                                   (for [[n [sx sy]] passengers]
                                     [(str "(passx " n " x" sx ")")
                                      (str "(passy " n " y" sy ")")])))
         "  )
           (:goal (and "
              (util/str-join " " (apply concat
                                   (for [[n _ [dx dy]] passengers]
                                     [(str "(passx " n " x" dx ")")
                                      (str "(passy " n " y" dy ")")])))
              ")))"]))))

(defn write-infinite-taxi-strips 
  ([tenv] (write-infinite-taxi-strips tenv (str "/tmp/inf-taxi" (rand-int 10000))))
  ([tenv prefix]
     (write-infinite-taxi-strips-domain (str prefix "-domain.pddl"))
     (write-infinite-taxi-strips-instance tenv (str prefix ".pddl"))
     prefix))

(deftest infinite-taxi-generic
  (is (= -15 (second (exp.ucs/uniform-cost-search (sas/make-sas-problem-from-pddl (write-infinite-taxi-strips (InfiniteTaxiEnv 5 5 [['red [2 1] [5 4]] ['green [1 4] [3 3]]]))))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This version doesn't split X and Y, to make DAG.

(defn- write-infinite-taxi-strips2-domain [file]
  (util/spit file
    ";; Taxi domain 
     
     (define (domain infinite-taxi2)
       (:requirements :typing)
       (:types loc pass)
       (:constants InTaxi - loc)
       (:predicates 
          (LEFTOF ?l1 ?l2 - loc)
          (ABOVE  ?l1 ?l2 - loc)
          (at ?l - loc)
          (passat ?p - pass ?l - loc))

       
       (:action pickup 
         :parameters (?p - pass ?l - loc)
         :precondition (and (at ?l) (passat ?p ?l))
         :effect       (and (not (passat ?p ?l)) (passat ?p InTaxi)))
                          
       (:action putdown 
         :parameters (?p - pass ?l - loc)
         :precondition (and (at ?l) (passat ?p InTaxi))
         :effect       (and (not (passat ?p InTaxi)) (passat ?p ?l)))

       (:action left 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (at ?l1) (LEFTOF ?l2 ?l1))
         :effect       (and (not (at ?l1)) (at ?l2)))

       (:action right 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (at ?l1) (LEFTOF ?l1 ?l2))
         :effect       (and (not (at ?l1)) (at ?l2)))

       (:action up 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (at ?l1) (ABOVE ?l2 ?l1))
         :effect       (and (not (at ?l1)) (at ?l2)))

       (:action down 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (at ?l1) (ABOVE ?l1 ?l2))
         :effect       (and (not (at ?l1)) (at ?l2))))"         
        ))

(defn- write-infinite-taxi-strips2-instance [tenv file]
  (let [{:keys [width height passengers]} tenv]
    (util/spit file
      (util/str-join "\n"
        ["(define (problem infinite-taxi2-)
           (:domain infinite-taxi2)
           (:objects "
              (util/str-join " " (map first passengers)) " - pass"
              (util/str-join " " (for [w (range 1 (inc width)) h (range 1 (inc height))] (str w "-" h)))
                             " - loc"
         "    )
           (:init "
              (util/str-join " " (for [w (range 1 width) h (range 1 (inc height))] 
                                   (str "(LEFTOF " w "-" h " " (inc w) "-" h ")")))
              (util/str-join " " (for [w (range 1 (inc width)) h (range 1 height)] 
                                   (str "(ABOVE " w "-" (inc h) " " w "-" h ")")))
              "(at 1-1)"
              (util/str-join " " (for [[n [sx sy]] passengers]
                                   (str "(passat " n " " sx "-" sy ")")))
              ")
           (:goal (and ;(at 1-1)"
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(passat " n " " dx "-" dy ")")))
              ")))"]))))

(defn write-infinite-taxi-strips2 
  ([tenv] (write-infinite-taxi-strips2 tenv (str "/tmp/inf-taxi2" (rand-int 10000))))
  ([tenv prefix]
     (write-infinite-taxi-strips2-domain (str prefix "-domain.pddl"))
     (write-infinite-taxi-strips2-instance tenv (str prefix ".pddl"))
     prefix))

(deftest infinite-taxi-generic2
  (is (= -15 (second (exp.ucs/uniform-cost-search (sas/make-sas-problem-from-pddl (write-infinite-taxi-strips2 (InfiniteTaxiEnv 5 5 [['red [2 1] [5 4]] ['green [1 4] [3 3]]]))))))))

; (make-sas-problem-from-pddl (prln (write-taxi-strips (make-random-taxi-env 1 2 1))) )
