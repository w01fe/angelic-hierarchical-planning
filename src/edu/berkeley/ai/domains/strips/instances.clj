(in-ns 'edu.berkeley.ai.domains.strips)

;;; STRIPS problem instances
;; TODO: normalize schema instances!


;; Problem instance structures and parsing.   

(defstruct strips-planning-instance :class :name :domain :objects :trans-objects :init-atoms :goal-atoms)

(defn make-strips-planning-instance [name domain objects init-atoms goal-atoms]
  (let [types           (:types domain)
	guaranteed-objs (:guaranteed-objs domain)
	predicates      (:predicates domain)
	all-objects     (props/check-objects types (concat objects guaranteed-objs))]
    (struct strips-planning-instance ::StripsPlanningInstance
	    name
	    domain
	    all-objects    
	    (util/map-map (fn [t] [t (mapcat (partial get all-objects) (props/get-subtypes types t))]) (keys types))
	    (concat (map (partial props/check-atom types all-objects predicates) init-atoms)
		    (map #(props/check-atom types all-objects predicates (cons (goal-ize (first %)) (rest %))) goal-atoms))
	    (map (partial props/check-atom types all-objects predicates) goal-atoms))))

(defn- parse-pddl-objects [s]
  (when s
    (let [[objs rst] (split-with (partial not= '-) s)]
      (util/assert-is (>= (count rst) 2))
      (cons [(second rst) objs]
	    (parse-pddl-objects (nthrest rst 2))))))

(defn read-strips-planning-instance [domain file]
  (util/match [[define [problem [unquote name]]
	   [:domain  [unquote domain-name]]
	   [:objects [unquote-seq objects]]
	   [:init    [unquote-seq init-facts]]
	   [:goal    [unquote goal-conj]]]
	  (read-string (.toLowerCase (slurp file)))]
    (util/assert-is (= domain-name (:name domain)))
    (make-strips-planning-instance
     name
     domain
     (parse-pddl-objects objects)
     init-facts
     (props/pddl-conjunction->seq goal-conj))))


;; Methods for Environment interface

(defmethod envs/get-initial-state ::StripsPlanningInstance [instance]
  (envs/metafy-initial-state    (set (:init-atoms instance))))
 
(defn get-strips-predicate-instantiations [instance]
  (for [[pred args] (:predicates (:domain instance))
	combo       (util/combinations (map #(util/safe-get (:trans-objects instance) %) args))]
    (cons pred combo)))

(defmethod envs/get-state-space   ::StripsPlanningInstance [instance]
  (binary-states/make-binary-state-space (get-strips-predicate-instantiations instance)))
 


(defn get-strips-action-schema-instance [schema var-map]
;  (prn schema var-map)
  (let [simplifier #(map (partial props/simplify-atom var-map) %)]
    (make-strips-action-schema
     (cons (:name schema) (map #(util/safe-get var-map (second %)) (:vars schema)))
     nil
     (simplifier (:pos-pre schema))
     (simplifier (:neg-pre schema))
     (simplifier (:add-list schema))
     (simplifier (:delete-list schema))
     (:cost schema))))

(defn get-strips-action-schema-instantiations [action-schema objects]
;  (prn action-schema) (util/prln
  (map (partial get-strips-action-schema-instance action-schema)
       (for [combo (util/combinations (map #(util/safe-get objects (first %)) (:vars action-schema)))]
	 (util/map-map (fn [[t v] val] [v val]) (:vars action-schema) combo))))

(defn strips-action->action [schema]
  (util/assert-is (empty? (:vars schema)))
  (envs/make-action 
   (:name schema)
   (fn [state]
     [(clojure.set/union 
       (clojure.set/difference state (:delete-list schema)) 
       (:add-list schema))
      (- (:cost schema))])
   (envs/make-conjunctive-condition (:pos-pre schema) (:neg-pre schema))))

;; TODO: speed up
(defmethod envs/get-action-space  ::StripsPlanningInstance [instance]
  (let [domain  (:domain instance)
	objects (:trans-objects instance)
	schemas (:action-schemata domain)
	instantiations (map #'strips-action->action 
			    (mapcat #(get-strips-action-schema-instantiations % objects)
				    schemas))]
    (envs/make-enumerated-action-space instantiations)))

   

(defmethod envs/get-goal          ::StripsPlanningInstance [instance]
  (envs/make-conjunctive-condition (:goal-atoms instance) nil))


;; useful utility 

(defn get-strips-state-pred-val "Get the only true args of pred in state, or error" [state pred]
  (let [pred-apps (filter #(= (first %) pred) state)]
    (util/assert-is (= (count pred-apps) 1))
    (rfirst pred-apps)))
  




(comment 
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl")
  )


(comment 
  (map :name (first (a-star-search 
  (state-space-search-node  
  (read-strips-planning-instance
   (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
   "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/probBLOCKS-4-0.pddl") (constantly 0)))))
  
  
  )


