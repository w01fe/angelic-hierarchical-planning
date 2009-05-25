(in-ns 'edu.berkeley.ai.angelic.hierarchies)

;;; Hierarchies
; Neat handling of high-level preconditions (be careful, can mess up equality -- use sets?)
;; HLAs may be hashed, etc, so should be sure to be canonical.

; Hierarchy is responsible for handling the goal now, e.g., by a finish action.
; Every plan should reach at most one state, *finish-state*, defined in descriptions-and-valuations.

;; Parsing

(defmulti parse-hierarchy-type (fn [type contents domain] type))

(defn parse-hierarchy "Call this method to parse a hierarchy.  Will delegate based on declared type." [file domain]
  (util/match [(define (hierarchy ~name)
	    (:type ~type)
	    ~@meat)
	  (read-string (slurp file))] ;(.toLowerCase (slurp file)))]
    (util/assert-is (= name (:name domain)))
    (parse-hierarchy-type type meat domain)))


;; Methods

(defmulti #^{:doc "Take a hierarchy and instance and return an instantiated top-level HLA sequence."} 
  instantiate-hierarchy (fn [hierarchy instance] (:class hierarchy)))

(defmulti #^{:doc "Get the env associated with this instantiated HLA."} 
  hla-environment :class)

(defmulti #^{:doc "Get the default valuation type associated with this HLA"}
  hla-default-optimistic-valuation-type :class)

(defmulti #^{:doc "Get the default valuation type associated with this HLA"}
  hla-default-pessimistic-valuation-type :class)

(defmulti #^{:doc "Is the HLA primitive or noop?."} 
  hla-primitive? :class)

(defmulti #^{:doc "If this HLA is primitive, return the primitive action, else nil. 
                   Can return :noop, which must be filtered out."} 
  hla-primitive :class)

(defmulti hla-name                       :class)

; TODO: this way of doing things doubles up on calls to restrict.
(defmulti  #^{:doc "Get refinements compatible with this optimistic valuation, representing 
            the situation before doing this action *or apply its hierarchical preconditions*"} 
    hla-immediate-refinements      (fn [hla val] [(:class hla) (:class val)]))

(defmulti hla-hierarchical-preconditions :class)

(defmulti hla-optimistic-description     :class)

(defmulti hla-pessimistic-description    :class)


(defn get-hierarchy [file env]
  (instantiate-hierarchy 
   (parse-hierarchy file (envs/get-domain env))
   env))





(comment ; Not sure if this will be needed later. ..

  ; Search space for use with action hierarchies

  (defstruct hierarchical-search-space-struct :class :state-space :action-space :goal :top-level-action)

  (defn make-hierarchical-search-space- [state-space action-space goal top-level-action ]
    (struct hierarchical-search-space-struct ::HierarchicalSearchSpace state-space action-space goal top-level-action ))

  (defn hierarchical-search-space [env top-level-action] 
    (make-hierarchical-search-space- (envs/get-state-space env) (envs/get-action-space env) (envs/get-goal env) top-level-action))
  )
