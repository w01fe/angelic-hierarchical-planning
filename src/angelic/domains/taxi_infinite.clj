(ns angelic.domains.taxi-infinite
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]
            [angelic.sas :as sas]
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            angelic.hierarchy.util)
  (:import [java.util Random]))



(defn- make-left   [s]
  (let [cx     (state/get-var s '[atx])]
    (when (> cx 1) 
      (angelic.env.util.FactoredPrimitive. ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn- make-right  [s]
  (let [const (state/get-var s :const)
        width  (get const '[width])
        cx     (state/get-var s '[atx])]
    (when (< cx width)  
      (angelic.env.util.FactoredPrimitive. ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn- make-down  [s]
  (let [cy     (state/get-var s '[aty])]
    (when (> cy 1)
      (angelic.env.util.FactoredPrimitive. ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn- make-up    [s]
  (let [const (state/get-var s :const)
        height (get const '[height])
        cy     (state/get-var s '[aty])]
    (when (< cy height)
      (angelic.env.util.FactoredPrimitive. ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn- make-pickup  [s pass [x y]]
  (angelic.env.util.FactoredPrimitive. 
   ['pickup pass x y] 
   {['atx]        x     ['aty]        y
    ['passx pass] x     ['passy pass] y}
   {['passx pass] :taxi ['passy pass] :taxi}
   -1))

(defn- make-dropoff [s pass [x y]]
  (when pass 
    (angelic.env.util.FactoredPrimitive. 
     ['dropoff pass x y] 
     {['atx]        x     '[aty] y 
      ['passx pass] :taxi ['passy pass] :taxi}
     {['passx pass] x     ['passy pass] y}
     -1)))


(defrecord InfiniteTaxiEnv [width height passengers]
 env/Env
  (initial-state [_]
    (into {:const {['width] width ['height] height}
           ['atx] 1 ['aty] 1}
          (apply concat
            (for [[name [sx sy]] passengers]
              [[['passx name] sx] [['passy name] sy]]))))
  (actions-fn [_]
   (fn taxi-actions [s]
     (filter identity
       (apply concat 
         (map #(% s) [make-left make-right make-up make-down])
         (for [[pass] passengers x (range 1 (inc width)) y (range 1 (inc height))] 
           [(make-pickup s pass [x y]) (make-dropoff s pass [x y])])))))
  (goal-fn [this] 
    (let [goal-map (env/goal-map this)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))
 env/FactoredEnv
  (goal-map [_] 
    (into {} 
      (apply concat
        [[['atx] width] [['aty] height]]
        (for [[pass _ [dx dy]] passengers] 
          [[['passx pass] dx] [['passy pass] dy]])))))


(defn make-random-infinite-taxi-env 
  ([width height n-passengers] 
     (make-random-infinite-taxi-env width height n-passengers (rand-int 10000000)))
  ([width height n-passengers seed]
     (let [r (Random. seed)]
       (.nextDouble r) (.nextDouble r)
       (InfiniteTaxiEnv. width height
                (for [i (range n-passengers)]
                  [(symbol (str "pass" i))
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]])))))





;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy ;;;;;;;;;;;;;;;;;;;;;
; Mostly copied from taxi. 

(defrecord NavHLA [env dx dy]
  env/Action
  (action-name [_] ['nav dx dy])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{['atx] ['aty]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (and (= dx (state/get-var s ['atx])) 
             (= dy (state/get-var s ['aty])))
      [[]]
      (for [af [make-left make-right make-up make-down]
            :let [a (af s)]
            :when a]
        [a this])))
  (cycle-level- [_ s] 1)

  hierarchy/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (let [cx (state/get-var s ['atx])
          cy (state/get-var s ['aty])]
      {(state/set-var (state/set-var s ['atx] dx) ['aty] dy)
       (- 0 (util/abs (- dx cx)) (util/abs (- dy cy)))}))
  (pessimistic-map- [this s] (hierarchy/optimistic-map- this s)))

(defrecord InfiniteTaxiTLA [env context] 
  env/Action
  (action-name [_] ['top])
  (primitive? [_] false)  

  env/ContextualAction
  (precondition-context [_ s] context)

  hierarchy/HighLevelAction 
  (immediate-refinements- [this s]
    (let [held-p (set (filter #(= :taxi (state/get-var s ['passx (first %)])) (:passengers env)))
          src-p  (remove #(or (held-p %) (state/get-var s ['pass-served? (first %)])) (:passengers env))
          all-nxt (concat (for [[n _ [dx dy]] held-p] [(NavHLA. env dx dy) (make-dropoff :dummy n [dx dy])])
                          (for [[n [sx sy] _]  src-p] [(NavHLA. env sx sy) (make-pickup  :dummy n [sx sy])]))]
      (if (empty? all-nxt)
        (let [{:keys [width height]} env]
          [[(NavHLA. env width height) (env-util/make-finish-action env)]])
        (map #(conj (vec %1) this) all-nxt))))
   (cycle-level- [_ s] nil)

   hierarchy/ExplicitAngelicAction
   (optimistic-map- [_ s] {(state/set-vars s (env-util/make-finish-goal-state env))})
   (pessimistic-map- [_ s] {}))

(defn make-infinite-taxi-tla [env]
  (InfiniteTaxiTLA. env (util/keyset (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy [#^InfTaxiEnv env]
  (angelic.hierarchy.util.SimpleHierarchicalEnv.
   env
   [(make-infinite-taxi-tla env)]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical to above.

(defn- write-infinite-taxi-strips-domain [file]
  (spit file
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
    (spit file
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
           (:goal (and "  (str "(at " width "-" height ")")
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

(defn make-random-infinite-taxi-sas [& args]
  (sas/make-sas-problem-from-pddl (write-infinite-taxi-strips (apply make-random-infinite-taxi-env args)))
  )



;; TODO: this is buggy.



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This version doesn't split X and Y, to make DAG.

(defn- write-infinite-taxi-strips2-domain [file]
  (spit file
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
    (spit file
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
           (:goal (and " (str "(at " width "-" height ")")
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(passat " n " " dx "-" dy ")")))
              ")))"]))))

(defn write-infinite-taxi-strips2 
  ([tenv] (write-infinite-taxi-strips2 tenv (str "/tmp/inf-taxi2" (rand-int 10000))))
  ([tenv prefix]
     (write-infinite-taxi-strips2-domain (str prefix "-domain.pddl"))
     (write-infinite-taxi-strips2-instance tenv (str prefix ".pddl"))
     prefix))

(defn make-random-infinite-taxi-sas2 [& args]
  (sas/make-sas-problem-from-pddl (write-infinite-taxi-strips2 (apply make-random-infinite-taxi-env args)))
  )





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This version doesn't split X and Y, to make DAG, and only allows putdown at goal.

(defn- write-infinite-taxi-strips3-domain [file]
  (spit file
    ";; Taxi domain 
     
     (define (domain infinite-taxi3)
       (:requirements :typing)
       (:types loc pass)
       (:constants InTaxi - loc)
       (:predicates 
          (LEFTOF ?l1 ?l2 - loc)
          (ABOVE  ?l1 ?l2 - loc)
          (PASSGOAL ?p - pass ?l - loc)
          (at ?l - loc)
          (passat ?p - pass ?l - loc))

       
       (:action pickup 
         :parameters (?p - pass ?l - loc)
         :precondition (and (at ?l) (passat ?p ?l))
         :effect       (and (not (passat ?p ?l)) (passat ?p InTaxi)))
                          
       (:action putdown 
         :parameters (?p - pass ?l - loc)
         :precondition (and (at ?l) (PASSGOAL ?p ?l) (passat ?p InTaxi))
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

(defn- write-infinite-taxi-strips3-instance [tenv file]
  (let [{:keys [width height passengers]} tenv]
    (spit file
      (util/str-join "\n"
        ["(define (problem infinite-taxi3-)
           (:domain infinite-taxi3)
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
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(PASSGOAL " n " " dx "-" dy ")")))
              ")
           (:goal (and " (str "(at " width "-" height ")")
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(passat " n " " dx "-" dy ")")))
              ")))"]))))

(defn write-infinite-taxi-strips3 
  ([tenv] (write-infinite-taxi-strips3 tenv (str "/tmp/inf-taxi3" (rand-int 10000))))
  ([tenv prefix]
     (write-infinite-taxi-strips3-domain (str prefix "-domain.pddl"))
     (write-infinite-taxi-strips3-instance tenv (str prefix ".pddl"))
     prefix))


; (make-sas-problem-from-pddl (prln (write-taxi-strips (make-random-taxi-env 1 2 1))) )
