(in-ns 'edu.berkeley.ai.domains.strips)

;;; STRIPS domains

;; STRIPS action schemata

(defstruct strips-action-schema :class :name :vars :pos-pre :neg-pre :add-list :delete-list :cost)

(defn make-strips-action-schema [name vars pos-pre neg-pre add-list delete-list cost]
  (struct strips-action-schema ::StripsActionSchema name vars pos-pre neg-pre add-list delete-list cost))

(defn- parse-pddl-action-schema [action]
  (util/match [[:action       [unquote name]
	   :parameters   [unquote parameters]
	   :precondition [unquote precondition]
	   :effect       [unquote effect]]
	  action]
    (let [[adds deletes]    (props/parse-pddl-conjunction effect)
	  [pos-pre neg-pre] (props/parse-pddl-conjunction precondition)] 
      (make-strips-action-schema 
       name 
       (props/parse-typed-pddl-list parameters)
       pos-pre
       neg-pre
       adds
       deletes
       1))))


(defn- check-action-schema [types guaranteed-objs predicates action-schema] 
;  (.println System/out action-schema)
  (util/assert-is (not (map? (:vars action-schema))))
  (let [vars-and-objects (props/check-objects types (concat guaranteed-objs (:vars action-schema)))
	atom-checker (fn [atoms] (map #(props/check-atom types vars-and-objects predicates %) atoms))]
    (make-strips-action-schema 
     (:name action-schema)
     (:vars action-schema)
     (atom-checker (:pos-pre       action-schema))
     (atom-checker (:neg-pre       action-schema))
     (atom-checker (:add-list      action-schema))
     (atom-checker (:delete-list   action-schema))
     (:cost action-schema))))

(defn- check-action-schemata [types guaranteed-objs predicates action-schemata]
  (util/assert-is (apply distinct? (map :name action-schemata)))
  (map (partial check-action-schema types guaranteed-objs predicates) action-schemata))


	    
;; STRIPS domains

(defstruct strips-planning-domain :class :name :types :guaranteed-objs :predicates :action-schemata)


(defn goal-ize [pred-name] (util/symbol-cat 'goal- pred-name))

(defn de-goal [pred]
  (let [name (name (first pred))]
    (if (.startsWith name "goal-")
      (cons (symbol (.substring name 5))
	    (rest pred)))))

(defn add-goal-predicates [predicates]
  (let [all-preds (merge predicates (util/map-map (fn [[pred args]] [(goal-ize pred) args]) predicates))]
    (util/assert-is (= (count all-preds) (* 2 (count predicates))))
    all-preds))

(defn make-strips-planning-domain 
  "types are either single keywords/symbols or [union-keyword & constituent-types].  
     Empty constitutenty type is same as single keyword/symbol.
   guaranteed-objs is a seq of [type & objects]
   predicates are [predicate-keyword & argument-types] (or symbols?).
   action-schemata are instances of strips-action-schema."
  [name types guaranteed-objs predicates action-schemata]
;  (prn name types guaranteed-objs predicates action-schemata)
  (let [types (props/check-types types)
	guaranteed-objs (props/check-objects types guaranteed-objs)
        predicates (props/check-predicates types predicates)
        action-schemata (check-action-schemata types guaranteed-objs predicates action-schemata)]
    (struct strips-planning-domain 
	    ::StripsPlanningDomain name types guaranteed-objs 
	    (add-goal-predicates predicates) action-schemata)))

(defn read-strips-planning-domain [file]
  (util/match [[define [domain [unquote name]]
	   [:requirements :strips :typing]
	   [:types [unquote-seq types]]
	   [:predicates [unquote-seq predicates]]
	   [unquote-seq actions]]
	  (read-string (.toLowerCase (slurp file)))]
    (make-strips-planning-domain 
     name
     types
     nil
     (map props/parse-pddl-predicate predicates)
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


;;; PDDL domain parsing helpers 




;(defn- emit-pddl-action-schema [action-schema]
;  (str "(:action " (:name action-schema) "\n"
;       "\n\t :parameters " 
;       "\n\t :precondition " (cons 'and (:precondition action-schema))
;       "\n\t :effect " (cons 'and (concat (:add-list action-schema)
;					  (map (partial list 'not) (:delete-list action-schema))))))s
