(in-ns 'edu.berkeley.ai.domains.strips)


;; TODO: normalize schema instances!

;;; Helpers for parsing instances



(defn- parse-pddl-objects [s]
  (when s
    (let [[objs rst] (split-with (partial not= '-) s)]
      (assert-is (>= (count rst) 2))
      (cons [(second rst) objs]
	    (parse-pddl-objects (nthrest rst 2))))))
     

;;; Helpers for implementing Environment interface (specifically, action space)
 

(defn- instantiate-schema [schema var obj rest-vars]
  (make-strips-action-schema 
   (concat (enforce-seq (:name schema)) [obj])
   rest-vars
   (map (partial simplify-atom var obj) (:preconditions schema))
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
    :preconditions (:preconditions schema)))

		      

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
	    (map (partial check-atom types all-objects predicates) init-atoms)
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
       (filter #(every? state (:preconditions %))
	       instantiations)))))
   

(defmethod get-goal          ::StripsPlanningInstance [instance]
  (let [goal-atoms (set (:goal-atoms instance))]
    (assoc (make-goal #(every? % goal-atoms))
     :conjuncts goal-atoms)))
  









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