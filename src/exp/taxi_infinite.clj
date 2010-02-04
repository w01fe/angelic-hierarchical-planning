(ns exp.taxi-infinite
  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [sas :as sas] [taxi :as taxi]])
  (:import [java.util Random]))


(defn make-pickup  [s pass [x y]]
  (env/FactoredPrimitive 
   ['pickup pass x y] 
   {['atx]        x     ['aty]        y
    ['passx pass] x     ['passy pass] y}
   {['passx pass] :taxi ['passy pass] :taxi}
   -1))

(defn make-dropoff [s pass [x y]]
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
         (map #(% s) [taxi/make-left taxi/make-right taxi/make-up taxi/make-down])
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

(defn write-infinite-taxi-strips-domain [file]
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
         :precondition (and (atx ?x) (aty ?y)
                            (passx ?p ?x)      (passy ?p ?y))
         :effect       (and (passx ?p InTaxiX) (passy ?p InTaxiY)))
                          
       (:action putdown 
         :parameters (?p - pass ?x - x ?y - y)
         :precondition (and (atx ?x) (aty ?y)
                            (passx ?p InTaxiX) (passy ?p InTaxiY))
         :effect       (and (passx ?p ?x)      (passy ?p ?y)))
                          
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

(defn write-infinite-taxi-strips-instance [tenv file]
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
              (util/str-join " " (for [y (range 1 height)] (str "(ABOVE y"  y " y" (inc y) ")")))              
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

; (make-sas-problem-from-pddl (prln (write-taxi-strips (make-random-taxi-env 1 2 1))) )
