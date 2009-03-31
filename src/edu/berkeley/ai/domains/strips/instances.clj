(in-ns 'edu.berkeley.ai.domains.strips)

;;; STRIPS problem instances
;; MAYBE: normalize schema instances! (see next)
;; MAYBE: - Identify duplicate actions and remove them
;; MAYBE - Identify constant atoms and remove them (pg)
;; MAYBE - In instance, remove atoms that never appear in precs / goals (backwards planning graph?)


;; Helpers for making instances

 
(defn get-predicate-instantiations [predicates trans-objects]
  (for [[pred args] predicates
	combo       (apply util/cartesian-product (map #(util/safe-get trans-objects %) args))]
    (into [pred] combo)))
;    (cons pred combo)))

(defn get-strips-action-schema-instance [schema var-map]
;  (prn schema var-map)
  (let [simplifier (fn [x] (map #(props/simplify-atom var-map %) x))]
    (make-strips-action-schema
     (into [(:name schema)] (map #(util/safe-get var-map (second %)) (:vars schema)))
     nil
     (simplifier (:pos-pre schema))
     (simplifier (:neg-pre schema))
     (simplifier (:add-list schema))
     (simplifier (:delete-list schema))
     (if (number? (:cost schema)) 
         (:cost schema)
       (apply (:cost-fn schema) (map #(util/safe-get var-map (second %)) (:vars schema))))
     nil)))

(defn- get-strips-action-instantiations  [action-schemata all-objects]
  (for [schema action-schemata,
	combo (apply util/cartesian-product (map #(util/safe-get all-objects (first %)) (:vars schema)))]
    (get-strips-action-schema-instance schema 
      (util/map-map (fn [[t v] val] [v val]) (:vars schema) combo))))


;; Problem instance structures and parsing.   

(derive ::StripsPlanningInstance ::envs/PropositionalEnvironment)

(defstruct strips-planning-instance :class :name :domain :objects :trans-objects :init-atoms :goal-atoms :all-atoms :all-actions :state-str-fn)

(defn- make-strips-planning-instance- [name domain objects trans-objects init-atoms goal-atoms all-atoms all-actions state-str-fn]
  (with-meta 
   (struct strips-planning-instance ::StripsPlanningInstance name domain objects trans-objects init-atoms goal-atoms all-atoms all-actions state-str-fn)
   {:domain-size-cache (util/sref {})}))

(defn make-strips-planning-instance 
  ([name domain objects init-atoms goal-atoms]
     (make-strips-planning-instance name domain objects init-atoms goal-atoms str))
  ([name domain objects init-atoms goal-atoms state-str-fn]
  (let [equality?       (includes-equality? domain)
	types           (:types domain)
	guaranteed-objs (:guaranteed-objs domain)
	predicates      (:predicates domain)
	all-objects     (props/check-objects types (concat objects guaranteed-objs))]
    ;(println types guaranteed-objs predicates all-objects)
    (make-strips-planning-instance-
	    name
	    domain
	    all-objects    
	    (util/map-map (fn [t] [t (mapcat (partial get all-objects) (props/get-subtypes types t))]) (keys types))
	    (concat (map (partial props/check-atom types all-objects predicates) 
			 (concat init-atoms 
				 (when equality? (for [[t os] all-objects, o os] [(util/symbol-cat t '=) o o]))))
		    (map #(props/check-atom types all-objects predicates (cons (goal-ize (first %)) (next %))) goal-atoms))
	    (map (partial props/check-atom types all-objects predicates) goal-atoms)
	    (get-predicate-instantiations (:predicates domain) all-objects)
	    (get-strips-action-instantiations (util/safe-get domain :action-schemata) all-objects)
	    state-str-fn))))

(defn- parse-pddl-objects [s]
  (when s
    (let [[objs rst] (split-with (partial not= '-) s)]
      (util/assert-is (>= (count rst) 2))
      (cons [(second rst) objs]
	    (parse-pddl-objects (nthnext rst 2))))))

(defn read-strips-planning-instance [domain file]
  (util/match [[define [problem ~name]
	   [:domain  ~domain-name]
	   [:objects ~@objects]
	   [:init    ~@init-facts]
	   [:goal    ~goal-conj]]
	  (read-string (.toLowerCase (slurp file)))]
    (util/assert-is (= domain-name (:name domain)))
    (make-strips-planning-instance
     name
     domain
     (parse-pddl-objects objects)
     init-facts
     (props/pddl-conjunction->seq goal-conj))))


;; Methods for Environment interface

(defmethod envs/get-domain        ::StripsPlanningInstance [instance]
  (util/safe-get instance :domain))

(defmethod envs/get-initial-state ::StripsPlanningInstance [instance]
  (envs/metafy-initial-state    (util/to-set (:init-atoms instance))))

(defmethod envs/get-state-space   ::StripsPlanningInstance [instance]
  (binary-states/make-binary-state-space (util/safe-get instance :all-atoms) (:state-str-fn instance)))

(defn strips-action->action [schema]
  (util/assert-is (empty? (:vars schema)))
  (envs/make-action 
   (:name schema)
   (fn [state]
     [(util/union-coll 
       (util/difference-coll state (:delete-list schema)) 
       (:add-list schema))
      (- (:cost schema))])
   (envs/make-conjunctive-condition (:pos-pre schema) (:neg-pre schema))))

; Each pred has 3 options - yes, no, don't care.  Want to maximize # yes + no
; MAYBE: compile sequence of tests?
; MAYBE: optimize compilation speed (actually hard to do, I tried)
; Single pass through actions, make single ordering? (ditto)

(import '(java.util HashMap HashSet Arrays ArrayList))
(set! *warn-on-reflection* true)

; Idea: make table, for each atom, set of pos and neg actions?
; Intersect set of current actions with each...
(defn- get-next-atom [actions blacklist]
  (let [#^HashMap atom-counts (HashMap.)]
    (doseq [action actions]
      (doseq [p (:pos (:precondition action))]
	(.put atom-counts p (inc (or (.get atom-counts p) 0))))
      (doseq [n (:neg (:precondition action))]
	(.put atom-counts n (inc (or (.get atom-counts n) 0)))))
    (doseq [atom blacklist]
      (.remove atom-counts atom))
    (when-not (.isEmpty atom-counts)
      (key (util/first-maximal-element val atom-counts)))))


(defn- make-successor-generator 
  ([actions] (make-successor-generator actions nil))
  ([actions blacklist]
;  (prn (count actions) blacklist)
  (util/timeout)
  (let [most-common-atom (get-next-atom actions blacklist)]
    (if (nil? most-common-atom) 
        (fn [state] actions)
      (let [pos-list (ArrayList.)
	    neg-list (ArrayList.)
	    dc-list  (ArrayList.)]
	(doseq [action actions]
	  (let [in-pos? (contains? (:pos (:precondition action)) most-common-atom)
		in-neg? (contains? (:neg (:precondition action)) most-common-atom)]
	    (cond (and in-pos? in-neg?) (prn "Warning: contradictory preconditions for action" action) 
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

         
(defmethod envs/get-action-space  ::StripsPlanningInstance [instance]
  (let [instantiations (map #'strips-action->action (util/safe-get instance :all-actions))]
    (envs/make-enumerated-action-space 
     instantiations
     (make-successor-generator instantiations)
     )))

(defmethod envs/get-goal          ::StripsPlanningInstance [instance]
  (envs/make-conjunctive-condition (:goal-atoms instance) nil))

;(defmethod envs/state-str  ::StripsPlanningInstance [env state] (envs/state-str (envs/(str state))  



;;; Constant predicate-simplified strips domain and modified methods.

(defn- get-cps-strips-action-instantiations  [action-schemata all-objects fluent-atoms always-true-atoms instance]
  (let [allowed-pred-inst-maps 
	  [[(reduce (fn [m atom] (util/assoc-cons m (first atom) atom)) {} always-true-atoms)
	    (reduce (fn [m atom] (util/assoc-cons m (first atom) atom)) {} fluent-atoms)]]]
;    (println allowed-pred-inst-maps)
    (filter identity
      (util/forcat [schema action-schemata]
        (let [{:keys [name vars pos-pre neg-pre add-list delete-list cost]} schema
	      unk-domains (util/map-map (fn [[t v]] [v (set (util/safe-get all-objects t))]) vars)
  	      csp (smart-csps/create-smart-csp pos-pre neg-pre {} unk-domains {} instance)]
;	  (println "Just made csp for action " (:name schema))
;	  (throw (IllegalArgumentException.))
;	  (println name vars pos-pre neg-pre unk-domains)
	  (for [var-map (smart-csps/get-smart-csp-solutions csp {} allowed-pred-inst-maps)]
	    (let [simplifier (fn [x] (set (filter fluent-atoms (map #(props/simplify-atom var-map %) x))))
		  pos-pre (simplifier pos-pre)
		  neg-pre (simplifier neg-pre)
		  add-list (simplifier add-list)
		  delete-list (simplifier delete-list)]
	      (when (empty? (util/intersection pos-pre neg-pre))
		(make-strips-action-schema
		 (into [name] (map #(util/safe-get var-map (second %)) vars))
		 nil pos-pre neg-pre add-list delete-list 
		 (if (number? cost) 
		     cost
		   (apply (:cost-fn schema) (map #(util/safe-get var-map (second %)) vars)))
		 nil)))))))))


(defn constant-predicate-simplify [instance]
  (util/assert-is (= (:class instance) ::StripsPlanningInstance))
  (let [domain (constant-annotate-strips-planning-domain (util/safe-get instance :domain))
	pred-map (util/safe-get domain :predicates)
	{const-preds :const-predicates, pi-preds :pi-predicates, ni-preds :ni-predicates} domain
	trans-objects (util/safe-get instance :trans-objects)
	goal-atoms    (util/to-set (util/safe-get instance :goal-atoms))
;	all-const-atoms  (util/to-set (get-predicate-instantiations (util/restrict-map pred-map const-preds) trans-objects))
;	all-ni-atoms     (util/to-set (get-predicate-instantiations (util/restrict-map pred-map ni-preds)    trans-objects))
	{reg-init :reg, const-init :const, pi-init :pi, ni-init :ni}
 	  (util/group-by (fn [atom]
			   (let [pred (first atom)]
			     (cond (contains? const-preds pred) :const
				   (contains? pi-preds pred)    :pi
				   (contains? ni-preds pred)    :ni
				   :else                        :reg)))
			 (util/safe-get instance :init-atoms))
	always-true-atoms (util/union-coll (set const-init) pi-init)
;	always-false-atoms (util/union-coll (util/difference-coll all-const-atoms const-init)
;					    (util/difference-coll all-ni-atoms    ni-init))
	fluent-atoms      (util/to-set (get-predicate-instantiations (apply dissoc pred-map const-preds) trans-objects))
	fluent-goal-atoms (util/difference goal-atoms always-true-atoms)]
;	   (util/difference
;		    (util/to-set (util/safe-get instance :all-atoms))
;		    (util/union always-true-atoms always-false-atoms))]
;    (util/assert-is (empty? (util/intersection always-true-atoms always-false-atoms)))
;    (util/assert-is (empty? (util/intersection always-false-atoms goal-atoms)))
    (util/assert-is (not-any? #(contains? const-preds (first %)) fluent-goal-atoms))
    (util/assert-is (empty? pi-preds))  ; For now, since
    (util/assert-is (empty? ni-preds))  ; smart-csp doesn't support this.
    (assoc
      (make-strips-planning-instance- 
       (util/safe-get instance :name)
       domain
       (util/safe-get instance :objects)
       (util/safe-get instance :trans-objects)
       reg-init
       (seq fluent-goal-atoms)
       fluent-atoms
       (get-cps-strips-action-instantiations (util/safe-get-in instance [:domain :action-schemata])
					     trans-objects fluent-atoms always-true-atoms instance)
       (util/safe-get instance :state-str-fn))
      :always-true-atoms always-true-atoms 
;      :always-false-atoms always-false-atoms
      :const-pred-map (util/map-vals set (reduce (fn [m pred] (util/assoc-cons m (nth pred 0) pred)) {} always-true-atoms)))))






;;; Flattened STRIPS instances

(defn- flatten-action [action flattener]
  (util/assert-is (empty? (util/safe-get action :vars)))
  (make-strips-action-schema 
   (util/safe-get action :name)
   nil
   (flattener (util/safe-get action :pos-pre)) 
   (flattener (util/safe-get action :neg-pre)) 
   (flattener (util/safe-get action :add-list)) 
   (flattener (util/safe-get action :delete-list)) 
   (util/safe-get action :cost)
   nil))

(import '(java.util HashMap))

(defn flatten-strips-instance [instance]
  (let [forward-map  (HashMap.),
	backward-map (HashMap.),
	cur-num      (util/sref 0),
	flattener #(doall
		    (for [a %] 
		      (or (.get forward-map a)
			  (let [sym (keyword (str @cur-num))]
			    (util/sref-up! cur-num inc)
			    (.put forward-map a sym)
			    (.put backward-map sym a)
			    sym))))]
    (assoc
      (make-strips-planning-instance-
       (util/safe-get instance :name)
       [:flattened (util/safe-get instance :domain)]
       nil
       nil
       (flattener (util/safe-get instance :init-atoms))
       (flattener (util/safe-get instance :goal-atoms))
       (flattener (util/safe-get instance :all-atoms))
       (map #(flatten-action % flattener) (util/safe-get instance :all-actions))
       (util/safe-get instance :state-str-fn))
      :unflatten-map (into {} backward-map))))
   

      	        

   
  

;; useful utility 

(defn get-strips-state-pred-val "Get the only true args of pred in state, or error" [state pred]
  (let [pred-apps (filter #(= (first %) pred) state)]
    (util/assert-is (= (count pred-apps) 1))
    (nfirst pred-apps)))
  
;; Instantiated variables are limited to allowed tuples ... positions are 0-indexed.
(defmethod envs/expected-domain-size ::StripsPlanningInstance [inst pred arg-pos inst-pos]
  (let [mem (util/safe-get ^inst :domain-size-cache)
	args [pred arg-pos (set inst-pos)]]
;    (println pred arg-pos inst-pos)
    (if-let [e (find (util/sref-get mem) args)]
        (val e)
      (let [atoms (or (get (:const-pred-map inst) pred) 
		  (filter #(= (first %) pred) (:init-atoms inst)))
	    val 
	      (if (empty? atoms) 0
  	        (apply util/mean
		 (map (fn [tuples] (count (distinct (map #(nth % arg-pos) tuples))))
		      (vals
		       (util/group-by (fn [tuple] (util/vec-map #(nth tuple %) inst-pos)) atoms)))))]
	(util/sref-set! mem (assoc (util/sref-get mem) args val))
	val))))



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








(comment  ;another try -- seems liek above is better.
(defn- make-successor-generator 
  ([actions] 
     (doall actions)
     (let [atom-order (get-successor-atom-order actions)
	   pos-set-map (HashMap.)
	   neg-set-map (HashMap.)
	   bad-actions (HashSet.)]
       (time (doseq [action actions]
	 (let [pos (:pos (:precondition action))
	       neg (:neg (:precondition action))]
	   (if (seq (util/intersection pos neg))
	       (.add bad-actions action)
	     (do 
	       (doseq [p pos] (.put pos-set-map p (conj (or (.get pos-set-map p) #{}) action)))
	       (doseq [n neg] (.put neg-set-map n (conj (or (.get neg-set-map n) #{}) action))))))))
       (time (make-successor-generator 
	      (util/difference-coll (set actions) bad-actions)
	      atom-order pos-set-map neg-set-map))))
  ([actions atom-order #^HashMap pos-set-map #^HashMap neg-set-map]
  (util/timeout)
  (if (empty? atom-order) (fn [state] actions)
    (let [most-common-atom (first atom-order)
	  pos-actions (util/intersection actions (.get pos-set-map most-common-atom))
	  neg-actions (util/intersection actions (.get neg-set-map most-common-atom))
	  dc-actions  (util/difference actions pos-actions neg-actions)
	  pos-branch (if (seq pos-actions) (make-successor-generator pos-actions (next atom-order) pos-set-map neg-set-map) (constantly nil))
	  neg-branch (if (seq neg-actions) (make-successor-generator neg-actions (next atom-order) pos-set-map neg-set-map) (constantly nil))
	  dc-branch  (if (seq dc-actions)  (make-successor-generator dc-actions  (next atom-order) pos-set-map neg-set-map) (constantly nil))]
      (cond (and (empty? dc-actions) (empty? neg-actions) (empty? pos-actions)) (throw (IllegalArgumentException.))
	    (and (empty? neg-actions) (empty? pos-actions)) dc-branch
	    :else 
	(fn [state] (concat (if (contains? state most-common-atom) (pos-branch state) (neg-branch state)) (dc-branch state))))))))
)