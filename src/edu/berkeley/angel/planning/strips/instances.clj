(in-ns 'edu.berkeley.angel.planning.strips)

(defstruct strips-planning-instance :class :name :domain :objects :trans-objects :init-atoms :goal-atoms)

(defn get-subtypes [types type]
  (when type
    (cons type 
	  (map get-subtypes (safe-get types type)))))

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
	    (map (partial check-atom types all-objects predicates) init-atoms)
	    (map (partial check-atom types all-objects predicates) goal-atoms))))

(defn parse-pddl-objects [s]
  (when s
    (let [[objs rst] (split-with (partial not= '-) s)]
      (assert-is (>= (count rst) 2))
      (cons [(second rst) objs]
	    (parse-pddl-objects (nthrest rst 2))))))

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
     

(comment 
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
  )
    

(defmethod instantiate-planning-domain ::StripsPlanningDomain 
  [domain objects init-facts goal]
  (make-strips-planning-instance nil domain objects init-facts goal))

(defn simplify-atom [var obj atom]
  (cons (first atom) (replace {var obj} (rest atom)))) 

(defn instantiate-schema [schema var obj rest-vars]
  (make-strips-action-schema 
   (concat (enforce-seq (:name schema)) [obj])
   rest-vars
   (map (partial simplify-atom var obj) (:preconditions schema))
   (map (partial simplify-atom var obj) (:add-list schema))
   (map (partial simplify-atom var obj) (:delete-list schema))
   (:cost schema)))

(defn get-instantiations [action-schema objects]
  (let [vars (seq (:vars action-schema))]
    (if (empty? vars) 
        [action-schema]
      (mapcat 
       #(get-instantiations 
	 (instantiate-schema action-schema (second (first vars)) % (rest vars))
	 objects)
       (get objects (ffirst vars))))))

(defn strips-action->action [schema]
  (assert-is (empty? (:vars schema)))
  (make-action 
   (:name schema)
   (fn [state]
     [(clojure.set/union 
       (clojure.set/difference state (:delete-list schema)) 
       (:add-list schema))
      (- (:cost schema))])))

(defn get-strips-action-space [instance]
  (let [domain  (:domain instance)
	objects (:trans-objects instance)
	schemas (:action-schemata domain)]
    (make-action-space
     (fn [state]
       (map strips-action->action
	    (filter #(every? state (:preconditions %))
		    (mapcat #(get-instantiations % objects)
			    schemas)))))))
		      
    
    

(defn get-strips-goal [instance]
  (let [goal-atoms (set (:goal-atoms instance))]
     (make-goal #(every? % goal-atoms))))

(defn strips-instance->state-space-search-problem 
  [instance]
  (make-search-problem 
   (set (:init-atoms instance)) 
   nil  
   (get-strips-action-space instance)
   (get-strips-goal instance)
   ))

(defmethod planning-problem->state-space-search-problem :edu.berkeley.angel.planning.strips/StripsPlanningInstance
  [instance]
  (make-search-problem 
   (set (:init-atoms instance)) 
   nil  
   (get-strips-action-space instance)
   (get-strips-goal instance)
   ))


(comment 
  (uniform-cost-graph-search 
  (strips-instance->state-space-search-problem 
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")))
  )