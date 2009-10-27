(ns edu.berkeley.ai.envs.hybrid-strips
 (:use     edu.berkeley.ai.util.hybrid)
 (:require [edu.berkeley.ai.util 
	    [hybrid :as hybrid] [propositions :as props] [intervals :as iv]
		[linear-expressions :as le]]
           [edu.berkeley.ai [util :as util] [envs :as envs]]
	   [edu.berkeley.ai.envs.hybrid-strips 
	    	[constraints :as hc]
	    	[effects :as he]]
           [edu.berkeley.ai.envs.states.binary :as binary-states])
 )



;;; Hybrid STRIPS domains
; In addition to usual features, have set of (real) numeric types and 
; set of numeric functions (otherwise like predicates).
; Numbers can be compared with the special predicates "=", "<", "<=", ">", ">=",
  ; negation not allowed.
; Linear functions of numbers are allowed.
; Effect literals for numbers take form (= (num-fn ...) new-value).
; Preconditions may include (forall (binding-params) (when) (precond)) forms.

; Right now, specific syntactic restrictions on constraints:
 ; Numeric vars can only appear in the left side of a comparison, not in expressions
   ; (except cost), and not in conditions of foralls
 ; The set of applicable discrete conditions must be computable statically,
   ; i.e., when in a forall, must have no condition.

;; STRIPS action schemata

;; TODO: add constant simplification ?


;;; States are [discrete-atoms numeric-vals]


;; Action Schemata


(defstruct hybrid-strips-action-schema 
  :class :name :vars :split-points :precondition :effect :cost-expr)

(defn make-hybrid-action-schema [name vars split-points precondition effect cost-expr]
  (struct hybrid-strips-action-schema ::HybridActionSchema 
    name vars split-points precondition effect cost-expr))

(defn- parse-hybrid-action-schema [action discrete-types numeric-types predicates numeric-functions constant-numeric-functions]
;  (println action discrete-types numeric-types predicates numeric-functions)
  (util/match [[[:action       ~name]
		[:parameters   ~parameters]
		[:optional [:split-points ~split-points]]
		[:precondition ~precondition]
		[:effect       ~effect]
		[:optional [:cost  ~cost]]]
	       (util/partition-all 2 action)]
    (let [vars (props/parse-typed-pddl-list parameters)
	  [discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types) ]
 ;     (println vars discrete-vars numeric-vars)
      (util/assert-is (<= (count numeric-vars) 1))
      (make-hybrid-action-schema
       name
       vars 
       (hc/parse-and-check-constraint split-points discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions true)
       (hc/parse-and-check-constraint precondition discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions true)
       (he/parse-and-check-effect     effect       discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions)
       (le/parse-and-check-hybrid-linear-expression (or cost 1) discrete-vars numeric-vars numeric-functions constant-numeric-functions)))))

(defn- effected-functions [action] 
  (he/effected-functions (util/safe-get (into {} (map vec (util/partition-all 2 action))) :effect)))

;(defn- ground-hybrid-action-schema [schema disc-var-map const-num-fns]
;  (assoc schema 
;    :split-points (hc/ground-hybrid-constraint (:split-points schema) disc-var-map const-num-fns)
;    :precondition (hc/ground-hybrid-constraint (:precondition schema) disc-var-map const-num-fns)
;    :effect       (he/ground-hybrid-effect     (:effect schema)       disc-var-map const-num-fns)
;    :cost-expr    (le/ground-hybrid-linear-expr (:cost-expr schema)   disc-var-map const-num-fns)))


	    
;;; Hybrid-strips domains

; discrete-types and numeric-types are sets of types (no inheritance for now)
; predicates is a map from predicate names to seqs of argument types
; numeric-functions is a map from function names to seqs of argument types (return type being dropped for now).
; action-schemata is a map from schema names to schema objects

(derive ::HybridStripsPlanningDomain ::envs/PropositionalDomain)

(defstruct hybrid-strips-planning-domain 
  :class :name :discrete-types :numeric-types :predicates :numeric-functions :action-schemata :equality?
  :constant-predicates :constant-numeric-functions)

(defn- make-hybrid-strips-planning-domain 
  [name discrete-types numeric-types predicates numeric-functions action-schemata equality? constant-predicates constant-functions]
  (struct hybrid-strips-planning-domain ::HybridStripsPlanningDomain
	  name discrete-types numeric-types predicates numeric-functions action-schemata equality? constant-predicates constant-functions))

(defn- check-numeric-functions [numeric-functions discrete-type-map numeric-types]
  (let [tl (props/parse-typed-pddl-list numeric-functions)]
    (doseq [[t f] tl] (util/assert-is (contains? numeric-types t)))
    (props/check-predicates discrete-type-map (map #(props/parse-pddl-predicate (second %)) tl))))

(defn read-hybrid-strips-planning-domain [file]
  (util/match [[define [domain ~name]
		[:requirements ~@requirements]
		[:types ~@discrete-types]
		[:numeric-types ~@numeric-types]
		[:predicates ~@predicates]
		[:numeric-functions ~@numeric-functions]
		~@actions]
	       (read-string (.toLowerCase (slurp file)))]
    (util/assert-is (apply distinct? discrete-types))
    (util/assert-is (apply distinct? numeric-types))
    (let [requirements   (set requirements)
	  discrete-types (set discrete-types)
	  numeric-types  (set numeric-types)
	  equality?      (contains? requirements :equality)
	  discrete-type-map (into {} (map vector discrete-types (repeat nil)))
	  predicates     (props/check-predicates discrete-type-map
			   (concat (map props/parse-pddl-predicate predicates)
			     (when equality? (map #(vector (util/symbol-cat % '=) % %) discrete-types))))
	  numeric-functions (check-numeric-functions numeric-functions discrete-type-map numeric-types)
	  constant-numeric-fns (util/difference (util/keyset numeric-functions)
					(apply util/union (map effected-functions actions)))
	  action-schemata   (map #(parse-hybrid-action-schema % discrete-types numeric-types predicates numeric-functions constant-numeric-fns)
				 actions)]
      (util/assert-is (util/subset? requirements #{:strips :typing :equality :numbers}))
      (util/assert-is (util/subset? #{:strips :typing :numbers} requirements))
      (util/assert-is (empty? (util/intersection discrete-types numeric-types)))
      (doseq [p (concat (keys predicates) (keys numeric-functions))] 
	(util/assert-is (not (contains? '#{= < <= > >= * + -} p))))
      (util/assert-is (apply distinct? (concat (keys predicates) (keys numeric-functions))))
      (util/assert-is (apply distinct? (map :name action-schemata)))
      (make-hybrid-strips-planning-domain 
       name
       discrete-types
       numeric-types
       predicates
       numeric-functions
       (into {} (map #(vector (util/safe-get % :name) %) action-schemata))
       equality?
       (util/difference (util/keyset predicates)
	 (apply util/union 
	   (for [as action-schemata]
	     (he/effected-predicates (:effect as)))))
       constant-numeric-fns
       ))))
 


 
;  (read-hybrid-strips-planning-domain "/Users/jawolfe/Projects/angel/src/edu/berkeley/ai/domains/hybrid_blocks.pddl")


;;; State space.

(derive ::HybridStateSpace ::edu.berkeley.ai.envs/StateSpace)

(defstruct hybrid-state-space :class :fluent-atoms :numeric-atoms :str-fn) 

(defn make-hybrid-state-space [fluent-atoms numeric-atoms str-fn]
  (struct hybrid-state-space ::HybridStateSpace (util/to-set fluent-atoms) (util/to-set numeric-atoms) str-fn))

(defmethod edu.berkeley.ai.envs/list-states ::HybridStateSpace [state-set]
  (throw (UnsupportedOperationException.)))

(defmethod edu.berkeley.ai.envs/canonicalize ::HybridStateSpace [state-set]
  state-set)  

(defmethod edu.berkeley.ai.envs/set-contains? ::HybridStateSpace [state-set elt]
  (and (every? (:fluent-atoms state-set) (first elt))
       (= (set (keys (second elt))) (:numeric-atoms state-set))))



;; Actions and action space


; Instantiated actions

;(defstruct hybrid-strips-action :schema :var-map)

(defn hybrid-strips-action->action [schema var-map action-space]
;  (println var-map)
  (let [effect (util/safe-get schema :effect)
	cost-expr (util/safe-get schema :cost-expr)]
    (envs/make-action 
     (vec (cons (:name schema) (map #(util/safe-get var-map (second %)) (:vars schema))))
     (fn [state] 
       [(he/execute-effect effect var-map state)
	(- (le/evaluate-hybrid-linear-expr cost-expr var-map (second state)))])
     (hc/make-constraint-condition (util/safe-get schema :precondition) (util/safe-get action-space :objects) var-map false))))

(defn get-hs-action 
  ([instance full-name]
     (let [schema (util/safe-get-in instance [:domain :action-schemata (first full-name)])]
       (hybrid-strips-action->action schema (into {} (map #(vector (second %1) %2) (util/safe-get schema :vars) (rest full-name))) (:action-space instance))))
  ([instance name var-map]
     (hybrid-strips-action->action (util/safe-get-in instance [:domain :action-schemata name]) var-map (:action-space instance))))

; Quasi-instantiated actions


; Action space (TODO)


(import '(java.util HashMap HashSet Arrays ArrayList))
(set! *warn-on-reflection* true)

(defn- get-next-atom [actions blacklist]
  (let [#^HashMap atom-counts (HashMap.)]
    (doseq [action actions]
      (doseq [p (:pos action)] (.put atom-counts p (inc (or (.get atom-counts p) 0))))
      (doseq [n (:neg action)] (.put atom-counts n (inc (or (.get atom-counts n) 0)))))
    (doseq [atom blacklist] (.remove atom-counts atom))
    (when-not (.isEmpty atom-counts)
      (key (util/first-maximal-element val atom-counts)))))


(defn- make-successor-generator 
  ([actions] (make-successor-generator actions nil))
  ([actions blacklist]
  (util/timeout)
  (let [most-common-atom (get-next-atom actions blacklist)]
    (if (nil? most-common-atom) 
        (fn [state] actions)
      (let [pos-list (ArrayList.)
	    neg-list (ArrayList.)
	    dc-list  (ArrayList.)]
	(doseq [action actions]
	  (let [in-pos? (contains? (:pos action) most-common-atom)
		in-neg? (contains? (:neg action) most-common-atom)]
	    (cond (and in-pos? in-neg?) nil ;(prn "Warning: contradictory preconditions for action" action) 
		  (and in-pos? (not in-neg?)) (.add pos-list action)
		  (and in-neg? (not in-pos?)) (.add neg-list action)
		  :else                       (.add dc-list action))))
	(let [pos-actions (seq pos-list)
	      neg-actions (seq neg-list)
	      dc-actions  (seq dc-list)
	    next-blacklist (cons most-common-atom blacklist)
	    pos-branch (if pos-actions (make-successor-generator pos-actions next-blacklist) (constantly nil))
	    neg-branch (if neg-actions (make-successor-generator neg-actions next-blacklist) (constantly nil))
	    dc-branch  (if dc-actions  (make-successor-generator dc-actions  next-blacklist) (constantly nil))]
	(fn [state] (concat (if (contains? state most-common-atom) (pos-branch state) (neg-branch state)) (dc-branch state))))))))) 

(set! *warn-on-reflection* false)

       
(defstruct hybrid-action-space :class :discrete-generator :objects :discrete-grid-size)

(defstruct hybrid-strips-quasi-action :schema :var-map :pos :neg :num-vars :num)

(defn- make-hybrid-action-space [discrete-types objects action-schemata discrete-grid-size]
;  (println (first action-schemata));(map :effect action-schemata))
  (struct hybrid-action-space ::HybridActionSpace
	(make-successor-generator 
  	  (for [schema (vals action-schemata)
	        :let [{:keys [vars precondition]} schema
		      [d-vars n-vars] (split-with #(contains? discrete-types (first %)) vars)]
		args (apply util/cartesian-product (map #(util/safe-get objects (first %)) d-vars))]
            (let [var-map (into {} (map vector (map second d-vars) args))
                  [p n num] (hc/split-constraint precondition var-map objects)]
	      ;(println (:name schema) var-map p n)
              (struct hybrid-strips-quasi-action schema var-map (set p) (set n) (set (map second n-vars)) num))))
	objects
	discrete-grid-size))
    



(defmulti applicable-quasi-actions (fn [state action-space] (:class action-space)))

; TODO: prune empty intervals.

(defmethod applicable-quasi-actions ::HybridActionSpace has-applicable-quasi-actions [[discrete-atoms numeric-vals] action-space]
  (for [action ((:discrete-generator action-space) discrete-atoms)
	:let [{:keys [var-map num]} action ;(do (println (:name (:schema action)) (:var-map action)) action)
;	      action (ground-hybrid-action-schema var-map numeric-vals)
	      num (hc/get-numeric-yield num var-map (:objects action-space) [discrete-atoms numeric-vals])]
	:when num]
    (let [num-vars    (:num-vars action)]
;      (println "done")
      (util/assert-is (<= (count num-vars) 1))
      (if (empty? num-vars)
          (do (util/assert-is (empty? num))
	      (assoc action :num {}))
	(assoc action :num
 	  {(first num-vars) 
	   (reduce iv/intersect-intervals
		   iv/*real-line*
		   (for [c num]
		     (let [{:keys [pred left right]} c
			   lval (le/extract-singleton-var left)
			   rval (le/extract-constant right)]
		       (util/assert-is (isa? (:class c) ::hc/NumConstraint))
		       (util/assert-is (and lval (not (coll? lval))))
		       (assert rval)
		       (util/assert-is (= (first num-vars) lval))
		       (condp = pred
			 =  (iv/make-interval rval false rval false)
			 <  (iv/make-interval Double/NEGATIVE_INFINITY true rval true)
			 <= (iv/make-interval Double/NEGATIVE_INFINITY true rval false)
			 >  (iv/make-interval rval true Double/POSITIVE_INFINITY true)
			 >= (iv/make-interval rval false Double/POSITIVE_INFINITY true)))))})))))


(defn quasi-action-numeric-intervals [action] ; Returns map from num-vars to intervals.
  (:num action))
		 
(defn ground-quasi-action 
  ([action num-var-map action-space]
     (util/assert-is (every? num-var-map (:num-vars action)))
     (hybrid-strips-action->action (:schema action) (merge num-var-map (:var-map action)) 
				   action-space)))

(defn discrete-quasi-action-instantiations [action action-space grid]
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (let [[var interval]  (first (:num action))]
 ;     (println (:name (:schema action)) (:var-map action) var interval)
      (for [i (iv/interval-grid-points interval grid)]		     
	(ground-quasi-action action {var i} action-space)))))

;; TODO: this specificity doesn't belong here.
(defn split-quasi-action-instantiations [[discrete-atoms numeric-vals] action action-space]
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (let [[var interval]   (first (:num action))
	  split-constraint (util/safe-get-in action [:schema :split-points])
	  split-clauses    (hc/get-numeric-yield split-constraint 
			     (:var-map action) 
			     (:objects action-space) 
			     [discrete-atoms numeric-vals])
	  split-points     (distinct 
			    (for [c split-clauses]
			      (let [{:keys [class pred left right]} c
				    lval (le/extract-singleton-var left)
				    rval (le/extract-constant right)]
				(util/assert-is (= class ::hc/NumConstraint))
				(util/assert-is (= pred =))
				(util/assert-is (= lval var))
				(assert rval)
				rval)))]
    ;  (println (:name (:schema action)) (:var-map action) interval split-points)
      (for [x split-points 
	    :when (iv/interval-contains? interval x)]
	(ground-quasi-action action {var x} action-space)))))

      

(defn all-quasi-action-instantiations [action action-space]
 ; (println (:name (:schema action)) (:var-map action))
  (if (empty? (:num-vars action))
      [(ground-quasi-action action nil action-space)]
    (repeatedly #(ground-quasi-action action
				      (util/map-vals iv/interval-rand (:num action))
				      action-space))))

(defn applicable-discrete-actions [[discrete-atoms numeric-vals] action-space grid]
 ; (println "discrete")
  (mapcat #(discrete-quasi-action-instantiations % action-space grid)
	  (applicable-quasi-actions [discrete-atoms numeric-vals] action-space)))

(defn applicable-split-actions [[discrete-atoms numeric-vals] action-space]
 ; (println "split")
  (mapcat #(split-quasi-action-instantiations [discrete-atoms numeric-vals] % action-space)
	  (applicable-quasi-actions [discrete-atoms numeric-vals] action-space)))

(defmethod envs/applicable-actions ::HybridActionSpace [state action-space]
  (if (:discrete-grid-size action-space) 
      (applicable-discrete-actions state action-space (:discrete-grid-size action-space))
    (applicable-split-actions state action-space)))

(defmethod envs/all-actions ::HybridActionSpace [action-space]
  (throw (UnsupportedOperationException.)))


; Tricky - for now, punt and require single numeric variable, not appearing in forall conditions.
; Build a little successor generator for finding consistent instantiations of discrete vars?
; Ignore yield of forall, just look at discrete 

; First stage: ground out discrete vars, run through successor generator 
 
; Second stage: for each action, collect conjunction of numeric constraints
; Separate into constraints involving numeric vars and others
; Filter on evaluation of others, and return set of quasi-ground actions

; Third stage: Instantiate ground action with numeric value

;;; Instances

(derive ::HybridStripsPlanningInstance ::envs/PropositionalEnvironment)
(defstruct hybrid-strips-planning-instance 
  :class :name :domain :objects :init-atoms :init-fns :goal-atoms :fluent-atoms :state-space :action-space :constant-numeric-vals)
  
(defn- get-instantiations [thing-map objects]
  (for [[n types] thing-map,
	args (apply util/cartesian-product (map #(util/safe-get objects %) types))]
    (vec (cons n args))))

(defn make-hybrid-strips-planning-instance
  ([name domain objects init-atoms init-fns goal-atoms]
     (make-hybrid-strips-planning-instance name domain objects init-atoms init-fns goal-atoms str nil))
  ([name domain objects init-atoms init-fns goal-atoms state-str-fn discrete-grid-size]
 ;    (println objects init-atoms init-fns goal-atoms)
     (let [{:keys [discrete-types numeric-types predicates numeric-functions action-schemata equality? constant-numeric-functions]} domain
	   discrete-type-map (into {} (map #(vector % nil) discrete-types))
	   objects (props/check-objects discrete-type-map objects)
	   object-type-map (into {} (for [[t os] objects, o os] [o t]))
	   all-atoms (set (get-instantiations predicates objects))]
       (doseq [nf-inst (get-instantiations numeric-functions objects)]
	 (when-not (number? (get init-fns nf-inst))
	   (util/print-debug 1 "Warning: No initial number for " nf-inst)))
;	 (util/assert-is (number? (get init-fns nf-inst))))
       (struct hybrid-strips-planning-instance ::HybridStripsPlanningInstance
	 name
	 domain
	 objects
	 (set 
	  (map #(check-hybrid-atom % predicates object-type-map)
	      (concat init-atoms
		      (when equality? (for [[t os] objects, o os] [(util/symbol-cat t '=) o o])))))
	 init-fns
	 (set (map #(check-hybrid-atom % predicates object-type-map) goal-atoms))
	 all-atoms
	 (make-hybrid-state-space all-atoms (util/keyset init-fns) state-str-fn)
	 (make-hybrid-action-space discrete-types objects action-schemata discrete-grid-size)
	 (into {} (filter #(contains? constant-numeric-functions (first (key %))) init-fns))
	 ))))



(defmethod envs/get-domain        ::HybridStripsPlanningInstance [instance]
  (util/safe-get instance :domain))

(defmethod envs/get-initial-state ::HybridStripsPlanningInstance [instance]
  (envs/metafy-initial-state [(:init-atoms instance) (:init-fns instance)]))

(defmethod envs/get-state-space   ::HybridStripsPlanningInstance [instance]
  (:state-space instance))

(defmethod envs/get-action-space  ::HybridStripsPlanningInstance [instance] 
  (:action-space instance))

(defmethod envs/get-goal          ::HybridStripsPlanningInstance [instance]
;  (println (:goal-atoms instance))
  (hc/make-constraint-condition
   (hc/make-conjunctive-constraint
    (map #(hc/make-discrete-pos-constraint %) (:goal-atoms instance)))
   nil 
   nil true))
;  (envs/make-conjunctive-condition (:goal-atoms instance) nil))
	
(defmethod envs/expected-domain-size ::HybridStripsPlanningInstance [inst pred arg-pos inst-pos]  
  (let [atoms (filter #(= (first %) pred) (util/safe-get inst :init-atoms))]
    (if (empty? atoms) 0
        (apply util/mean
               (map (fn [tuples] (count (distinct (map #(nth % arg-pos) tuples))))
                    (vals
                     (util/group-by (fn [tuple] (util/vec-map #(nth tuple %) inst-pos)) atoms)))))))   



