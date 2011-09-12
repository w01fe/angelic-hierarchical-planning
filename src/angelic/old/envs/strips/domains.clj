(in-ns 'angelic.old.envs.strips)

;;; STRIPS domains

;; STRIPS action schemata

; Cost is numeric cost, or expression.  Cost-fn is compiled fn from vars to numeric cost.
(defstruct strips-action-schema :class :name :vars :pos-pre :neg-pre :add-list :delete-list :cost :cost-fn)

(defn make-strips-action-schema [name vars pos-pre neg-pre add-list delete-list cost cost-fn]
  (struct strips-action-schema ::StripsActionSchema name vars pos-pre neg-pre add-list delete-list cost cost-fn))

(defn- parse-pddl-action-schema [action]
  (util/match [[[:action       ~name]
		[:parameters   ~parameters]
		[:precondition ~precondition]
		[:effect       ~effect]
		[:optional [:cost  ~cost]]]
	       (partition-all 2 action)]
    (let [[adds deletes]    (props/parse-pddl-conjunction effect)
	  [pos-pre neg-pre] (props/parse-pddl-conjunction precondition)] 
      (make-strips-action-schema 
       name 
       (props/parse-typed-pddl-list parameters)
       pos-pre
       neg-pre
       adds
       deletes
       (or cost 1)
       nil
       ))))


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
     (:cost action-schema)
     (binding [*ns* (find-ns 'angelic.old.envs.strips)]
       (eval `(fn strips-cost-fn ~(vec (map second (:vars action-schema))) ~(:cost action-schema))))
     )))

(defn- check-action-schemata [types guaranteed-objs predicates action-schemata]
  (util/assert-is (util/distinct-elts? (map :name action-schemata)))
  (map (partial check-action-schema types guaranteed-objs predicates) action-schemata))


	    
;; STRIPS domains

; types is a map from types to subtypes
; guaranteed-objs is a map from types to seqs of objects
; predicates is a map from predicate names to seqs of argument types
; action-schemata is a seq of action-schema objects

(derive ::StripsPlanningDomain ::envs/PropositionalDomain)

(defstruct strips-planning-domain :class :name :types :guaranteed-objs :predicates :action-schemata :equality?)

(defn goal-ize [pred-name] (util/symbol-cat 'goal- pred-name))

;(defn de-goal [pred]
;  (let [name (name (first pred))]
;    (if (.startsWith name "goal-")
;      (assoc pred 0 (symbol (.substring name 5))))))

(defn- includes-equality? [domain] (:equality? domain))

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
  [name types guaranteed-objs predicates action-schemata include-equality?]
;  (prn name types guaranteed-objs predicates action-schemata)
;  (println types)
  (let [;all-type (gensym "all-type")
	;prim-types (map #(if (coll? %) (first %) %) 
	;		(filter #(or (not (coll? %)) (empty? (next %))) types))
	types (props/check-types types) ;(if include-equality? (cons [all-type prim-types] types) types))
	guaranteed-objs (props/check-objects types guaranteed-objs)
        predicates (props/check-predicates types 
		    (concat predicates
		     (when include-equality? (map #(vector (util/symbol-cat (first %) '=) (first %) (first %)) types))))
        action-schemata (check-action-schemata types guaranteed-objs predicates action-schemata)]
    (struct strips-planning-domain ::StripsPlanningDomain
	    name types guaranteed-objs 
	    (add-goal-predicates predicates) action-schemata include-equality?
	    )))

(defn read-strips-planning-domain [file]
  (util/match [[define [domain ~name]
		[:requirements ~@requirements]
		[:types ~@types]
		[:optional [:auxillary-fluents ~@aux]]
		[:predicates ~@predicates]
		~@actions]
	       (read-string (.toLowerCase (slurp file)))]
    (let [requirements (set requirements)]
      (util/assert-is (util/subset? requirements #{:strips :typing :equality}))
      (util/assert-is (util/subset? #{:strips :typing} requirements))
      (assoc
       (make-strips-planning-domain 
	name
	types
	nil
	(map props/parse-pddl-predicate predicates)
	(map parse-pddl-action-schema actions)
	(contains? requirements :equality))
       :auxillary-fluents aux))))


;; Identify constant/inertia preds

; const-predicates is seq of predicate names from (keys :predicates) that are not changed by any action.  
; positive-predicates and negative-predicates are similar, but are ones that only appear positively or negatively (resp.) in any effect.
(defstruct ca-strips-planning-domain :class :name :types :guaranteed-objs :predicates :action-schemata :const-predicates :pi-predicates :ni-predicates :equality?)
(derive ::CAStripsPlanningDomain ::StripsPlanningDomain)

(defn constant-annotate-strips-planning-domain [domain]
  (if (isa? (:class domain) ::CAStripsPlanningDomain) domain
    (let [;equality?       (:equality? domain)
	  aux (util/safe-get domain :auxillary-fluents)
	  action-schemata (util/safe-get domain :action-schemata)
	  all-preds (util/keyset (util/safe-get domain :predicates))
	  add-preds (set (for [as action-schemata, add (util/safe-get as :add-list)] (first add)))
	  del-preds (set (for [as action-schemata, del (util/safe-get as :delete-list)] (first del)))]
;      (when equality? (util/assert-is (and (not add-preds '=) (not del-preds '=))))
      (util/assert-is (every? all-preds aux))
      (struct ca-strips-planning-domain ::CAStripsPlanningDomain
	(util/safe-get domain :name)
	(util/safe-get domain :types)
	(util/safe-get domain :guaranteed-objs)
	(util/safe-get domain :predicates)
	action-schemata
	(util/difference-coll 
	 (util/difference (util/difference all-preds add-preds) del-preds) 
	 aux) 
;	(util/difference add-preds del-preds)
;	(util/difference del-preds add-preds)
	nil nil
	))))
	
  





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
  
  (read-strips-planning-domain "/Volumes/data/old/Users/jawolfe/Projects/research/IPC/IPC2/2000-Tests/Blocks/Track1/Typed/domain.pddl")
)





;(defn- emit-pddl-action-schema [action-schema]
;  (str "(:action " (:name action-schema) "\n"
;       "\n\t :parameters " 
;       "\n\t :precondition " (cons 'and (:precondition action-schema))
;       "\n\t :effect " (cons 'and (concat (:add-list action-schema)
;					  (map (partial list 'not) (:delete-list action-schema))))))s
