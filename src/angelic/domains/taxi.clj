(ns angelic.domains.taxi
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.sas :as sas]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))

(defn- make-left   [s]
  (let [cx     (state/get-var s '[atx])]
    (when (> cx 1) 
      (env-util/make-factored-primitive ['left cx]  {['atx] cx} {['atx] (dec cx)} -1))))

(defn- make-right  [s]
  (let [const (state/get-var s :const)
        width  (get const '[width])
        cx     (state/get-var s '[atx])]
    (when (< cx width)  
      (env-util/make-factored-primitive ['right cx] {['atx] cx} {['atx] (inc cx)} -1))))

(defn- make-down  [s]
  (let [cy     (state/get-var s '[aty])]
    (when (> cy 1)
      (env-util/make-factored-primitive ['down cy]  {['aty] cy} {['aty] (dec cy)} -1))))

(defn- make-up    [s]
  (let [const (state/get-var s :const)
        height (get const '[height])
        cy     (state/get-var s '[aty])]
    (when (< cy height)
      (env-util/make-factored-primitive ['up cy] {['aty] cy} {['aty] (inc cy)} -1))))

(defn- make-pickup  [s pass]
  (let [const (state/get-var s :const)]
    (env-util/make-factored-primitive 
     ['pickup pass] 
     {['atx] (get const ['srcx pass]) 
      ['aty] (get const ['srcy pass]) 
      ['pass-served? pass] false 
      ['in-taxi] nil}
     {['in-taxi] pass}
     -1)))

(defn- make-dropoff 
  ([s] (make-dropoff s (state/get-var s '[in-taxi])))
  ([s pass]
     (when pass 
       (let [const (state/get-var s :const)
             dx (get const ['dstx pass])
             dy (get const ['dsty pass])]
         (env-util/make-factored-primitive 
          ['dropoff pass] 
          {['atx] dx '[aty] dy '[in-taxi] pass}
          {'[in-taxi] nil ['pass-served? pass] true}
          -1)))))


(defrecord TaxiEnv [width height passengers] 
 env/Env
  (initial-state [_]
    (into {:const (into {['width] width ['height] height}
                      (apply concat
                       (for [[name [sx sy] [dx dy]] passengers]
                         [[['srcx name] sx] [['srcy name] sy]
                          [['dstx name] dx] [['dsty name] dy]])))
           ['atx] 1 ['aty] 1 ['in-taxi] nil}
          (for [[name [sx sy] [dx dy]] passengers]
            [['pass-served? name] (= [sx sy] [dx dy])])))
  (actions-fn [_]
   (fn taxi-actions [s]
     (filter identity
       (concat (map #(% s) [make-left make-right make-up make-down make-dropoff])
               (for [[pass] passengers] (make-pickup s pass))))))
  (goal-fn [this] 
    (let [goal-map (env/goal-map this)]
      #(when (state/state-matches-map? % goal-map)
         (env/solution-and-reward %))))

 env/FactoredEnv
  (goal-map [_] (into {} (for [[pass] passengers] [['pass-served? pass] true]))))


;; TODO: think about a sort of concentration parameter for common positions.
(defn make-random-taxi-env 
  ([width height n-passengers] 
     (make-random-taxi-env width height n-passengers (rand-int 10000000)))
  ([width height n-passengers seed]
     (let [r (Random. seed)]
       (.nextDouble r) (.nextDouble r)
       (TaxiEnv. width height
                (for [i (range n-passengers)]
                  [(symbol (str "pass" i))
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]
                   [(inc (.nextInt r width)) (inc (.nextInt r height))]])))))


; (use '[angelic env taxi search hierarchy])
; (uniform-cost-search (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]])) 

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
  
  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (let [cx (state/get-var s ['atx])
          cy (state/get-var s ['aty])]
      {(state/set-var (state/set-var s ['atx] dx) ['aty] dy)
       (- 0 (util/abs (- dx cx)) (util/abs (- dy cy)))}))
  (pessimistic-map- [this s] 
    (angelic/optimistic-map- this s)))

(defrecord GGNavHLA [env]
  env/Action
  (action-name [_] '[nav])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{['atx] ['aty]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (cons []
          (for [af [make-left make-right make-up make-down]
                :let [a (af s)]
                :when a]
            [a this])))
  (cycle-level- [_ s] 1))

(defmethod hierarchy/gg-action :angelic.taxi/NavHLA [a]
  [(GGNavHLA. (:env a)) {'[atx] (:dx a) '[aty] (:dy a)}])


(defrecord ServeHLA [env pass]
  env/Action
  (action-name [_] ['serve pass])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{ ['atx] ['aty] ['in-taxi] ['pass-served? pass]})

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [const (state/get-var s :const)
          [sx sy dx dy] 
          (map #(get const [% pass]) '[srcx srcy dstx dsty])
          pu (make-pickup  s pass)
          pd (make-dropoff s pass)]
      (util/assert-is (and pu pd))
      [[(NavHLA. env sx sy) pu (NavHLA. env dx dy) pd]]))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (let [const (state/get-var s :const)
          [cx cy] (map #(state/get-var s [%]) '[atx aty])
          [sx sy dx dy] (map #(get const [% pass]) '[srcx srcy dstx dsty])]
      {(state/set-vars s [[['atx] dx] [['aty] dy] [['pass-served? pass] true]])
       (- -2 
          (util/abs (- sx cx)) (util/abs (- sy cy))
          (util/abs (- sx dx)) (util/abs (- sy dy)))}))
  (pessimistic-map- [this s] 
    (angelic/optimistic-map- this s)))

(defn- taxi-hungarian-heuristic [env s] "destination-to-destination."
  (let [[cx cy] (map #(state/get-var s [%]) '[atx aty])
        pass    (remove #(state/get-var s ['pass-served? (first %)]) (:passengers env))]
    (if (empty? pass) 0
      (int (Math/floor 
         (util/maximum-matching
         (cons ::current (map first pass))
         (cons ::goal    (map first pass))
         (concat
          (for [[p1 _ [dx1 dy1]]         (cons [::current nil [cx cy]] pass)
                [p2 [sx2 sy2] [dx2 dy2]] pass]
            [p1 p2
             (- -2
                (util/abs (- dx1 sx2)) (util/abs (- dy1 sy2))
                (util/abs (- dx2 sx2)) (util/abs (- dy2 sy2)))])        
          (for [[p [sx sy] [dx dy]] pass]
            [p ::goal 0]))))))))

(defrecord TaxiTLA [env context]  
  env/Action
  (action-name [_] ['top])
  (primitive? [_] false)  

  env/ContextualAction
  (precondition-context [_ s] context)

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [remaining-passengers
          (for [[pass] (:passengers env)
                :when (not (state/get-var s ['pass-served? pass]))]
            pass)]
      (if (empty? remaining-passengers)
        [[(env-util/make-finish-action env)]]
        (for [pass remaining-passengers]
          [(ServeHLA. env pass) this]))))
  (cycle-level- [_ s] nil)
  
  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    {(state/set-vars s (env-util/make-finish-goal-state env))
     (taxi-hungarian-heuristic env s)})
  (pessimistic-map- [_ s] {}))

(defn- make-taxi-tla [env]
  (TaxiTLA. env (util/keyset (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy [^TaxiEnv env]
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(make-taxi-tla env)]))


(defn simple-taxi-hierarchy-nsa [^TaxiEnv env]
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(angelic.hierarchy.util.NSAHLA. (make-taxi-tla env) (util/keyset (dissoc (env/initial-state env) :const)))]))

; (uniform-cost-search (ShopHTNEnv (simple-taxi-hierarchy (TaxiEnv 5 5 [ ['bob [1 1] [3 3] ] ['mary [1 1] [3 3] ] ['lisa [1 1] [3 3] ]]))))



;; Slightly fancier hierarchy that splits navigation.
(defrecord NavHHLA [env dx]
  env/Action
  (action-name [_] ['navh dx])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{ ['atx]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (= dx (state/get-var s ['atx]))
      [[]]
      (for [af [make-left make-right]
            :let [a (af s)]
            :when a]
        [a this])))
  (cycle-level- [_ s] 1))

(defrecord NavVHLA [env dy]
  env/Action
  (action-name [_] ['navv dy])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{ ['aty]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (= dy (state/get-var s ['aty]))
      [[]]
      (for [af [make-up make-down]
            :let [a (af s)]
            :when a]
        [a this])))
  (cycle-level- [_ s] 1))

(defrecord Nav2HLA [env dx dy] 
  env/Action
  (action-name [_] ['nav dx dy])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{ ['atx] ['aty]})

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s] [[(NavHHLA. env dx) (NavVHLA. env dy)]])
  (cycle-level- [_ s] nil))

(defrecord Serve2HLA [env pass] 
  env/Action
  (action-name [_] ['serve pass])
  (primitive? [_] false)
  
  env/ContextualAction
  (precondition-context [_ s] #{ ['atx] ['aty] ['in-taxi] ['pass-served? pass]})
  
  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [const (state/get-var s :const)
          [sx sy dx dy] 
          (map #(get const [% pass]) '[srcx srcy dstx dsty])
          pu (make-pickup  s pass)
          pd (make-dropoff s pass)]2
      (util/assert-is (and pu pd))
      [[(Nav2HLA. env sx sy) pu (Nav2HLA. env dx dy) pd]]))
  (cycle-level- [_ s] nil))


(defrecord Taxi2TLA [env context]
  env/Action
  (action-name [_] ['top])
  (primitive? [_] false)
  
  env/ContextualAction
  (precondition-context [_ s] context)
  
  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [remaining-passengers
          (for [[pass] (:passengers env)
                :when (not (state/get-var s ['pass-served? pass]))]
            pass)]
      (if (empty? remaining-passengers)
        [[(env-util/make-finish-action env)]]
        (for [pass remaining-passengers]
          [(Serve2HLA. env pass) this]))))
  (cycle-level- [_ s] nil))

(defn- make-taxi-tla2 [env]
  (Taxi2TLA. env (util/keyset (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy2 [^TaxiEnv env]
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(make-taxi-tla2 env)]))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Yet another hierarchy that does away with Nav and just directly does h then v.

(defrecord Serve3HLA [env pass] 
  env/Action
  (action-name [_] ['serve pass])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{ ['atx] ['aty] ['in-taxi] ['pass-served? pass]})                            

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [const (state/get-var s :const)
          [sx sy dx dy] 
          (map #(get const [% pass]) '[srcx srcy dstx dsty])
          pu (make-pickup  s pass)
          pd (make-dropoff s pass)]
      (util/assert-is (and pu pd))
      [[(NavHHLA. env sx) (NavVHLA. env sy) pu 
        (NavHHLA. env dx) (NavVHLA. env dy) pd]]))
  (cycle-level- [_ s] nil))

(defrecord Taxi3TLA [env context]  
  env/Action
  (action-name [_] ['top])
  (primitive? [_] false)  

  env/ContextualAction
  (precondition-context [_ s] context)

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [remaining-passengers
          (for [[pass] (:passengers env)
                :when (not (state/get-var s ['pass-served? pass]))]
            pass)]
      (if (empty? remaining-passengers)
        [[(env-util/make-finish-action env)]]
        (for [pass remaining-passengers]
          [(Serve3HLA. env pass) this]))))
  (cycle-level- [_ s] nil))

(defn- make-taxi-tla3 [env]
  (Taxi3TLA. env (util/keyset (dissoc (env/initial-state env) :const))))

(defn simple-taxi-hierarchy3 [^TaxiEnv env]
  (hierarchy-util/make-simple-hierarchical-env
   env
   [(make-taxi-tla3 env)]))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Similar to above, except different encoding and re-picking pass is allowed.

(defn- write-taxi-strips-domain [file]
  (spit file
    ";; Taxi domain 
     
     (define (domain taxi)
       (:requirements :typing)
       (:types loc pass)
       (:constants InTaxi - loc)
       (:predicates 
          (LEFTOF ?l1 ?l2 - loc)
          (ABOVE  ?l1 ?l1 - loc)
          (taxi-at ?l)
          (pass-at ?p - pass ?l - loc)
          (pass-goal ?p - pass ?l - loc)
          (taxi-empty)
          (taxi-holding ?p - pass))
       
       (:action pickup 
         :parameters (?p - pass ?l - loc)
         :precondition (and 
                         (taxi-at ?l)
                         (pass-at ?p ?l)
                         (taxi-empty))
         :effect       (and
                         (not (taxi-empty)) (taxi-holding ?p)
                         (not (pass-at ?p ?l)) (pass-at ?p InTaxi)))
                          
       (:action putdown 
         :parameters (?p - pass ?l - loc)
         :precondition (and 
                         (taxi-at ?l)
                         (pass-at ?p InTaxi)
                         (taxi-holding ?p)
                         (pass-goal ?p ?l))
         :effect       (and
                         (not (taxi-holding ?p)) (taxi-empty)
                         (not (pass-at ?p InTaxi)) (pass-at ?p ?l)))

       (:action left 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (taxi-at ?l1) (LEFTOF ?l2 ?l1))
         :effect       (and (not (taxi-at ?l1)) (taxi-at ?l2)))

       (:action right 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (taxi-at ?l1) (LEFTOF ?l1 ?l2))
         :effect       (and (not (taxi-at ?l1)) (taxi-at ?l2)))

       (:action up 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (taxi-at ?l1) (ABOVE ?l2 ?l1))
         :effect       (and (not (taxi-at ?l1)) (taxi-at ?l2)))

       (:action down 
         :parameters (?l1 ?l2 - loc)
         :precondition (and (taxi-at ?l1) (ABOVE ?l1 ?l2))
         :effect       (and (not (taxi-at ?l1)) (taxi-at ?l2))))"
         
        ))

(defn- write-taxi-strips-instance [tenv file]
  (let [{:keys [width height passengers]} tenv]
    (spit file
      (util/str-join "\n"
        ["(define (problem taxi-)
           (:domain taxi)
           (:objects "
              (util/str-join " " (map first passengers)) " - pass"
              (util/str-join " " (for [w (range 1 (inc width)) h (range 1 (inc height))] (str w "-" h))) " - loc"
         "    )
           (:init "
              (util/str-join " " (for [w (range 1 width) h (range 1 (inc height))] 
                                   (str "(LEFTOF " w "-" h " " (inc w) "-" h ")")))
              (util/str-join " " (for [w (range 1 (inc width)) h (range 1 height)] 
                                   (str "(ABOVE " w "-" (inc h) " " w "-" h ")")))
              "(taxi-at 1-1)"
              (util/str-join " " (for [[n [sx sy]] passengers]
                                   (str "(pass-at " n " " sx "-" sy ")")))
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(pass-goal " n " " dx "-" dy ")")))
              "(taxi-empty))"
         " (:goal (and "
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(pass-at " n " " dx "-" dy ")")))
              ")))"]))))

(defn write-taxi-strips 
  ([tenv] (write-taxi-strips tenv (str "/tmp/taxi" (rand-int 10000))))
  ([tenv prefix]
     (write-taxi-strips-domain (str prefix "-domain.pddl"))
     (write-taxi-strips-instance tenv (str prefix ".pddl"))
     prefix))

(defn make-random-taxi-sas [& args]
  (sas/make-sas-problem-from-pddl (write-taxi-strips (apply make-random-taxi-env args))))

; (make-sas-problem-from-pddl (prln (write-taxi-strips (make-random-taxi-env 1 2 1))) )




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; STRIPS version 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical to above, but with split x and y.

(defn- write-taxi-strips2-domain [file]
  (spit file
    ";; Taxi domain 
     
     (define (domain taxi2)
       (:requirements :strips :typing)
       (:types x y pass)
       (:predicates 
          (LEFTOF ?x1 - x ?x2 - x)
          (ABOVE  ?y1 - y ?y2 - y)
          (taxi-at-x ?x - x)
          (taxi-at-y ?y - y)
          (pass-at-x ?p - pass ?x - x)
          (pass-at-y ?p - pass ?y - y)
          (pass-goal-x ?p - pass ?x - x)
          (pass-goal-y ?p - pass ?y - y)
          (taxi-empty)
          (taxi-holding ?p - pass))
       
       (:action pickup 
         :parameters (?p - pass ?x - x ?y - y)
         :precondition (and 
                         (taxi-at-x ?x) (taxi-at-y ?y)
                         (pass-at-x ?p ?x) (pass-at-y ?p ?y)
                         (taxi-empty))
         :effect       (and
                         (not (taxi-empty)) (taxi-holding ?p)
                         (not (pass-at-x ?p ?x)) (not (pass-at-y ?p ?y))))
                          
       (:action putdown 
         :parameters (?p - pass ?x - x ?y - y)
         :precondition (and 
                         (taxi-at-x ?x) (taxi-at-y ?y)
                         (taxi-holding ?p)
                         (pass-goal-x ?p ?x) (pass-goal-y ?p ?y))
         :effect       (and
                         (not (taxi-holding ?p)) (taxi-empty)
                         (pass-at-x ?p ?x) (pass-at-y ?p ?y)))

       (:action left 
         :parameters (?l1 - x ?l2 - x)
         :precondition (and (taxi-at-x ?l1) (LEFTOF ?l2 ?l1))
         :effect       (and (not (taxi-at-x ?l1)) (taxi-at-x ?l2)))

       (:action right 
         :parameters (?l1 - x ?l2 - x)
         :precondition (and (taxi-at-x ?l1) (LEFTOF ?l1 ?l2))
         :effect       (and (not (taxi-at-x ?l1)) (taxi-at-x ?l2)))

       (:action up 
         :parameters (?l1 - y ?l2 - y)
         :precondition (and (taxi-at-y ?l1) (ABOVE ?l2 ?l1))
         :effect       (and (not (taxi-at-y ?l1)) (taxi-at-y ?l2)))

       (:action down 
         :parameters (?l1 - y ?l2 - y)
         :precondition (and (taxi-at-y ?l1) (ABOVE ?l1 ?l2))
         :effect       (and (not (taxi-at-y ?l1)) (taxi-at-y ?l2))))"
         
        ))

(defn- write-taxi-strips2-instance [tenv file]
  (let [{:keys [width height passengers]} tenv]
    (spit file
      (util/str-join "\n"
        ["(define (problem taxi2-)
           (:domain taxi2)
           (:objects "
              (util/str-join " " (map first passengers)) " - pass"
              (util/str-join " " (for [x (range 1 (inc width))] (str "x" x))) " - x"              
              (util/str-join " " (for [y (range 1 (inc height))] (str "y" y))) " - y"                             "    )
           (:init "
              (util/str-join " " (for [x (range 1 width)] (str "(LEFTOF x" x " x" (inc x) ")")))
              (util/str-join " " (for [y (range 1 height)] (str "(ABOVE y" (inc y) " y" y ")")))         
              "(taxi-at-x x1) (taxi-at-y y1)"
              (util/str-join " " (for [[n [sx sy]] passengers]
                                   (str "(pass-at-x " n " x" sx ") (pass-at-y " n " y" sy ")")))
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(pass-goal-x " n " x" dx ") (pass-goal-y " n " y" dy ")")))      
              "(taxi-empty))"
         " (:goal (and "
              (util/str-join " " (for [[n _ [dx dy]] passengers]
                                   (str "(pass-at-x " n " x" dx ") (pass-at-y " n " y" dy ")")))
              ")))"]))))

(defn write-taxi-strips2
  ([tenv] (write-taxi-strips2 tenv (str "/tmp/taxi2_" (rand-int 10000))))
  ([tenv prefix]
     (write-taxi-strips2-domain (str prefix "-domain.pddl"))
     (write-taxi-strips2-instance tenv (str prefix ".pddl"))
     prefix))

(defn make-random-taxi-sas2 [& args]
  (sas/make-sas-problem-from-pddl (write-taxi-strips2 (apply make-random-taxi-env args))))