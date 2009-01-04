(in-ns 'edu.berkeley.angel.domains.strips)


;;; STRIPS action schemas

(defstruct strips-action-schema :class :name :vars :preconditions :add-list :delete-list :cost)

(defn make-strips-action-schema [name vars preconditions add-list delete-list cost]
  (struct strips-action-schema ::StripsActionSchema name vars preconditions add-list delete-list cost))


;;; STRIPS planning domain helpers

(defn- check-types [types]
  (let [type-map (map-map seq->vector-pair types)]
    (assert-is (= (count types) (count type-map)) "Duplicate type")
    (loop [type-map type-map]
      (let [next-type-map 
	    (map-map 
	     (fn [[k vs]] 
	       [k (mapcat 
		   (fn [v] 
		     (assert-is (not= k v) "Recursion detected") 
		     (or (safe-get type-map v) [v])) 
		   vs)]) 
	     type-map)]
	(if (= next-type-map type-map) type-map
	    (do (doseq [[k vs] next-type-map]
		  (assert-is (distinct-elts? vs) "Duplicate inclusion"))
		(recur next-type-map)))))
    type-map))

(defn- check-objects [types guaranteed-objs]
  (let [obj-map (reduce (fn [m [k & vs]] (assoc-cat m k (if (coll? (first vs)) (first vs) vs))) {} guaranteed-objs)]
    (doseq [k (keys obj-map)] (safe-get types k))
    (assert-is (distinct-elts? (apply concat (vals obj-map))))
    obj-map))


(defn- check-predicates [types predicates]
  (let [pred-map (map-map seq->vector-pair predicates)]
    (assert-is (= (count predicates) (count pred-map)) "Duplicate predicate")
    (doseq [[pred pred-types] pred-map,
	    pred-type pred-types]
      (safe-get types pred-type))
    pred-map))

(defn- is-type? [types objects obj type]
  (or (includes? obj (get objects type))
      (some (partial is-type? types objects obj) (get types type))))

(defn- check-type [types objects obj type]
  (assert-is (is-type? types objects obj type)))

(defn- check-atom [types objects predicates atom]
;  (prn atom)
  (let [[pred & args] atom,
	type-sig (safe-get predicates pred)]
    (assert-is (= (count args) (count type-sig)) "Wrong number of predicate args.")
    (doseq [[obj type] (map vector args type-sig)]
      (check-type types objects obj type))
    atom))

(defn- check-action-schema [types guaranteed-objs predicates action-schema] 
;  (.println System/out action-schema)
  (let [vars-and-objects (check-objects types (concat guaranteed-objs (:vars action-schema)))]
    (doseq [atom (concat (:preconditions action-schema)
			 (:add-list      action-schema)
			 (:delete-list   action-schema))]
;      (.println System/out atom)
      (check-atom types vars-and-objects predicates atom)))
  action-schema)

(defn- check-action-schemata [types guaranteed-objs predicates action-schemata]
  (assert-is (distinct-elts? (map :name action-schemata)))
  (map (partial check-action-schema types guaranteed-objs predicates) action-schemata))
    
;;; PDDL domain parsing helpers 

(defn- parse-typed-pddl-list [s]
  (when (seq s)
    (match [[[unquote v] - [unquote t] [unquote-seq rst]] s]
      (cons [t v]
	    (parse-typed-pddl-list rst)))))

(defn- parse-pddl-predicate [pred]
  (cons (first pred) (map first (parse-typed-pddl-list (rest pred)))))

(defn- pddl-conjunction->seq [conj]
  (if (= (first conj) 'and)
      (rest conj)
    (list conj)))

(defn- parse-pddl-action-schema [action]
  (match [[:action       [unquote name]
	   :parameters   [unquote parameters]
	   :precondition [unquote precondition]
	   :effect       [unquote effect]]
	  action]
    (let [[adds deletes] (separate #(not= (first %) 'not) (pddl-conjunction->seq effect))]
      (make-strips-action-schema 
       name 
       (parse-typed-pddl-list parameters)
       (pddl-conjunction->seq precondition)
       adds
       (map second deletes)
       1))))

	    
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