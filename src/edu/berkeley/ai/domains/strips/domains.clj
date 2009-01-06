(in-ns 'edu.berkeley.ai.domains.strips)


;;; STRIPS action schemas

(defstruct strips-action-schema :class :name :vars :pos-pre :neg-pre :add-list :delete-list :cost)

(defn make-strips-action-schema [name vars pos-pre neg-pre add-list delete-list cost]
  (struct strips-action-schema ::StripsActionSchema name vars pos-pre neg-pre add-list delete-list cost))


;;; STRIPS planning domain helpers

(defn- check-action-schema [types guaranteed-objs predicates action-schema] 
;  (.println System/out action-schema)
  (assert-is (not (map? (:vars action-schema))))
  (let [vars-and-objects (check-objects types (concat guaranteed-objs (:vars action-schema)))
	atom-checker (fn [atoms] (map #(check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-action-schema 
     (:name action-schema)
     (:vars action-schema)
     (atom-checker (:pos-pre       action-schema))
     (atom-checker (:neg-pre       action-schema))
     (atom-checker (:add-list      action-schema))
     (atom-checker (:delete-list   action-schema))
     (:cost action-schema))))

(defn- check-action-schemata [types guaranteed-objs predicates action-schemata]
  (assert-is (distinct-elts? (map :name action-schemata)))
  (map (partial check-action-schema types guaranteed-objs predicates) action-schemata))
    
;;; PDDL domain parsing helpers 


(defn- parse-pddl-action-schema [action]
  (match [[:action       [unquote name]
	   :parameters   [unquote parameters]
	   :precondition [unquote precondition]
	   :effect       [unquote effect]]
	  action]
    (let [[adds deletes]    (parse-pddl-conjunction effect)
	  [pos-pre neg-pre] (parse-pddl-conjunction precondition)] 
      (make-strips-action-schema 
       name 
       (parse-typed-pddl-list parameters)
       pos-pre
       neg-pre
       adds
       deletes
       1))))

;(defn- emit-pddl-action-schema [action-schema]
;  (str "(:action " (:name action-schema) "\n"
;       "\n\t :parameters " 
;       "\n\t :precondition " (cons 'and (:precondition action-schema))
;       "\n\t :effect " (cons 'and (concat (:add-list action-schema)
;					  (map (partial list 'not) (:delete-list action-schema))))))s


	    
;;; Actual STRIPS domain definition and interface

(defstruct strips-planning-domain :class :name :types :guaranteed-objs :predicates :action-schemata)

(defn make-strips-planning-domain 
  "types are either single keywords/symbols or [union-keyword & constituent-types].  
     Empty constitutenty type is same as single keyword/symbol.
   guaranteed-objs is a seq of [type & objects]
   predicates are [predicate-keyword & argument-types] (or symbols?).
   action-schemata are instances of strips-action-schema."
  [name types guaranteed-objs predicates action-schemata]
;  (prn name types guaranteed-objs predicates action-schemata)
  (let [types (check-types types)
	guaranteed-objs (check-objects types guaranteed-objs)
        predicates (check-predicates types predicates)
        action-schemata (check-action-schemata types guaranteed-objs predicates action-schemata)]
    (struct strips-planning-domain ::StripsPlanningDomain name types guaranteed-objs predicates action-schemata)))


(defn read-strips-planning-domain [file]
  (match [[define [domain [unquote name]]
	   [:requirements :strips :typing]
	   [:types [unquote-seq types]]
	   [:predicates [unquote-seq predicates]]
	   [unquote-seq actions]]
	  (read-string (.toLowerCase (slurp file)))]
    (make-strips-planning-domain 
     name
     types
     nil
     (map parse-pddl-predicate predicates)
     (map parse-pddl-action-schema actions))))





(comment 
  (is-type? {:typea nil, :typeb [:typea]} {:typea [:a1]} :a1 :typea)

  (make-strips-planning-domain "bla"
   [:typea :typeb [:typec [:typea :typeb]]]
   [[:typea :a1 :a2] [:typeb :b1] [:typec :c1]]
   [[:p0] [:p1a :typea] [:p2bc :typeb :typec]]
   [(make-strips-action-schema :Act1 [[:typea :a?] [:typeb :b?] [:typec :c?]] [[:p0] [:p1a :a?] [:p2bc :b? :c?]] [] [] 1)
    (make-strips-action-schema :Act2 [[:typea :a?] [:typeb :b?]] [[:p0] [:p1a :a?] [:p2bc :b? :a?]] [] [] 1)
    (make-strips-action-schema :Act3 [] [[:p0] [:p1a :a1] [:p2bc :b1 :b1]] [] [] 1)
     ])
  
  (read-strips-planning-domain "/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
)