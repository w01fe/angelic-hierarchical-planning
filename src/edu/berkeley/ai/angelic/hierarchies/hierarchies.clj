(in-ns 'edu.berkeley.ai.angelic.hierarchies)

;;; Hierarchies
; Neat handling of high-level preconditions (be careful, can mess up equality -- use sets?)


;; Parsing

(defmulti parse-hierarchy-type (fn [type contents domain] type))

(defn parse-hierarchy "Call this method to parse a hierarchy.  Will delegate based on declared type." [file domain]
  (match [(define (hierarchy [unquote name])
	    (:type [unquote type])
	    [unquote-seq meat])
	  (read-string (slurp file))] ;(.toLowerCase (slurp file)))]
    (assert-is (= name (:name domain)))
    (parse-hierarchy-type type meat domain)))


;; Methods

(defmulti instantiate-hierarchy (fn [hierarchy instance] (:class hierarchy)))

(defmulti #^{:doc "If this HLA is primitive, return the primitive action, else nil."} hla-primitive :class)

(defmulti hla-name                       :class)

; TODO: this way of doing things doubles up on calls to restrict.
(defmulti  #^{:doc "Get refinements compatible with this optimistic valuation, representing 
            the situation before doing this action *or apply its hierarchical preconditions*"} 
    hla-immediate-refinements      (fn [hla val] [(:class hla) (:class val)]))

(defmulti hla-hierarchical-preconditions :class)

(defmulti hla-optimistic-description     :class)

(defmulti hla-pessimistic-description    :class)





(comment ; Not sure if this will be needed later. ..

  ; Search space for use with action hierarchies
  ; TODO: have some debug level where we check that the action space matches what's generated top-down.

  (defstruct hierarchical-search-space-struct :class :state-space :action-space :goal :top-level-action)

  (defn make-hierarchical-search-space- [state-space action-space goal top-level-action ]
    (struct hierarchical-search-space-struct ::HierarchicalSearchSpace state-space action-space goal top-level-action ))

  (defn hierarchical-search-space [env top-level-action] 
    (make-hierarchical-search-space- (get-state-space env) (get-action-space env) (get-goal env) top-level-action))
  )
