(in-ns 'edu.berkeley.ai.domains.strips)


;; TODO: normalize schema instances!

;;; Conjunctive conditions

;; TODO: empty conditions

(derive ::ConjunctiveCondition :edu.berkeley.ai.envs/Condition)

(defstruct conjunctive-condition :class :pos :neg)
(defn make-conjunctive-condition [pos neg] 
  (struct conjunctive-condition ::ConjunctiveCondition (set pos) (set neg)))

;(defmulti get-positive-conjuncts :class)
(defn get-positive-conjuncts [c] (safe-get c :pos))

;(defmulti get-negative-conjuncts :class)
(defn get-negative-conjuncts [c] (safe-get c :neg))

(defmethod satisfies-condition? ::ConjunctiveCondition [s c]
  (and (every?   s (:pos c))
       (not-any? s (:neg c)))) 

(defmethod conjoin-conditions [::ConjunctiveCondition ::ConjunctiveCondition] [c1 c2]
  (make-conjunctive-condition 
   (clojure.set/union (get-positive-conjuncts c1) (get-positive-conjuncts c2))
   (clojure.set/union (get-negative-conjuncts c1) (get-negative-conjuncts c2))))
			      
(defn simplify-conjunctive-condition [c var-map]
  (make-conjunctive-condition
   (map (partial simplify-atom var-map) (get-positive-conjuncts c))
   (map (partial simplify-atom var-map) (get-negative-conjuncts c))))




;;; Helpers for parsing instances

(defn- parse-pddl-objects [s]
  (when s
    (let [[objs rst] (split-with (partial not= '-) s)]
      (assert-is (>= (count rst) 2))
      (cons [(second rst) objs]
	    (parse-pddl-objects (nthrest rst 2))))))
     

;;; Helpers for implementing Environment interface (specifically, action space)

;; TODO: standalone instantiate -> action method.

(defn- instantiate-schema [schema var obj rest-vars]
  (make-strips-action-schema 
   (concat (enforce-seq (:name schema)) [obj])
   rest-vars
   (map (partial simplify-atom var obj) (:pos-pre schema))
   (map (partial simplify-atom var obj) (:neg-pre schema))
   (map (partial simplify-atom var obj) (:add-list schema))
   (map (partial simplify-atom var obj) (:delete-list schema))
   (:cost schema)))

(defn- get-instantiations [action-schema objects]
  (let [vars (seq (:vars action-schema))]
    (if (empty? vars) 
        [action-schema]
      (mapcat 
       #(get-instantiations 
	 (instantiate-schema action-schema (second (first vars)) % (rest vars))
	 objects)
       (get objects (ffirst vars))))))



(defn- strips-action->action [schema]
  (assert-is (empty? (:vars schema)))
  (assoc 
      (make-action 
       (:name schema)
       (fn [state]
	 [(clojure.set/union 
	   (clojure.set/difference state (:delete-list schema)) 
	   (:add-list schema))
	  (- (:cost schema))]))
    :precondition (make-conjunctive-condition (:pos-pre schema) (:neg-pre schema))))

(defn- get-ground-tails [all-objects var-tail]
  (if (empty? var-tail) ['()]
    (for [tail   (get-ground-tails all-objects (rest var-tail))
	  object (safe-get all-objects (first var-tail))]
      (cons object tail))))
     
(defn get-ground-atoms [instance]
  (concat-elts 
   (for [[predicate arglist] (:predicates (:domain instance))]
     (map #(cons predicate %)
	  (get-ground-tails (:trans-objects instance) arglist)))))
		      

;;; Structure definition, methods, and implementation of Env interface.

(defstruct strips-planning-instance :class :name :domain :objects :trans-objects :init-atoms :goal-atoms)

(defn make-strips-planning-instance [name domain objects init-atoms goal-atoms]
  (let [types           (:types domain)
	guaranteed-objs (:guaranteed-objs domain)
	predicates      (:predicates domain)
	all-objects     (check-objects types (concat objects guaranteed-objs))]
    (struct strips-planning-instance ::StripsPlanningInstance
	    name
	    domain
	    all-objects    
	    (map-map (fn [t] [t (mapcat (partial get all-objects) (get-subtypes types t))]) (keys types))
	    (concat (map (partial check-atom types all-objects predicates) init-atoms)
		    (map #(check-atom types all-objects predicates (cons (goal-ize (first %)) (rest %))) goal-atoms))
	    (map (partial check-atom types all-objects predicates) goal-atoms))))

(defn read-strips-planning-instance [domain file]
  (match [[define [problem [unquote name]]
	   [:domain  [unquote domain-name]]
	   [:objects [unquote-seq objects]]
	   [:init    [unquote-seq init-facts]]
	   [:goal    [unquote goal-conj]]]
	  (read-string (.toLowerCase (slurp file)))]
    (assert-is (= domain-name (:name domain)))
    (make-strips-planning-instance
     name
     domain
     (parse-pddl-objects objects)
     init-facts
     (pddl-conjunction->seq goal-conj))))



(defmethod get-initial-state ::StripsPlanningInstance [instance]
  (metafy-initial-state    (set (:init-atoms instance))))
 
(defmethod get-state-space   ::StripsPlanningInstance [instance]
  (make-binary-state-space (:predicates instance)))
  
(defmethod get-action-space  ::StripsPlanningInstance [instance]
  (let [domain  (:domain instance)
	objects (:trans-objects instance)
	schemas (:action-schemata domain)
	instantiations (map #'strips-action->action 
			    (mapcat #(get-instantiations % objects)
				    schemas))]
    (make-action-space
     (fn [state]
       (filter #(satisfies-condition? state (:precondition %))
	       instantiations)))))
   
(defmethod get-goal          ::StripsPlanningInstance [instance]
  (make-conjunctive-condition (:goal-atoms instance) nil))





(comment 
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
  )


(comment 
  (map :name (first (uniform-cost-graph-search 
  (state-space-search-node  
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")))))
  
  
  )