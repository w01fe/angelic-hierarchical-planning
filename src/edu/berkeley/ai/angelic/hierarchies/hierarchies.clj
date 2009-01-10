(in-ns 'edu.berkeley.ai.angelic.hierarchies)

; Here, primitives are a type of high-level action.  

; Two ways to hande high-level preconditions; sloppy and neat.


; Two ideas

; One: angelic iwthout sets of states, just state abstraction?!

; Two: treat unbound HLA variables like a second level (do away with HLA preconditions) ?

; Collect preconditions in node with HLA (they are important).  But be careful, can mess up equality (set?)




;(defstruct high-level-action :class :hierarchy :hierarchical-preconditions :name )
;(defstruct primitive-high-level-action :class :hierarchy :hierarchical-preconditions :primitive)

; Generic stuff for hierarchies.  

(defmulti parse-hierarchy-type (fn [type contents domain] type))

(defn parse-hierarchy [file domain]
  (match [(define (hierarchy [unquote name])
	    (:type [unquote type])
	    [unquote-seq meat])
	  (read-string (slurp file))] ;(.toLowerCase (slurp file)))]
    (assert-is (= name (:name domain)))
    (parse-hierarchy-type type meat domain)))

(defmulti instantiate-hierarchy (fn [hierarchy instance] (:class hierarchy)))

;(derive ::PrimitiveHLA ::HLA)

(defmulti #^{:doc "If this HLA is primitive, return the primitive action, else nil."} hla-primitive :class)
(defmethod hla-primitive ::HLA [hla] nil)
;(defmethod hla-primitive ::PrimitiveHLA [hla] (:primitive hla))

(defmulti hla-name                       :class)
;(defmethod hla-name ::PrimitiveHLA [hla] (:name (hla-primitive hla)))


; TODO: this way of doing things doubles up on calls to restrict.
(defmulti  #^{:doc "Get refinements compatible with this optimistic valuation, representing 
            the situation before doing this action *or apply its hierarchical preconditions*"} 
    hla-immediate-refinements      (fn [hla val] [(:class hla) (:class val)]))
;(defmethod hla-immediate-refinements [::PrimitiveHLA ::Valuation] [hla] (throw (UnsupportedOperationException.)))

(defmulti hla-hierarchical-preconditions :class)
(defmulti hla-optimistic-description     :class)
(defmulti hla-pessimistic-description    :class)




; Search space for use with action hierarchies
; TODO: have some debug level where we check that the action space matches what's generated top-down.


(defstruct hierarchical-search-space-struct :class :state-space :action-space :goal :top-level-action)

(defn make-hierarchical-search-space- [state-space action-space goal top-level-action ]
  (struct hierarchical-search-space-struct ::HierarchicalSearchSpace state-space action-space goal top-level-action ))

(defn hierarchical-search-space [env top-level-action] 
  (make-hierarchical-search-space- (get-state-space env) (get-action-space env) (get-goal env) top-level-action))



;(defmul immediate-refinements (fn [hla state] :class)


(comment 
(defn plug [v pos subseq]
  (append (subvec v 0 pos)
	  subseq
	  (subvec v (inc pos))))
)

;(defmethod [act]
;  
; )


; this all goes in search-space, in amended form. abstract-lookahead-tree is search-space.

(comment 

(let [its (iterate #(subvec % 0 10) (apply vector (range 20)))] 
  (doseq [i (range 0 100 10)] 
    (print i " ")
    (let [sub (nth its i)]
      (time (dotimes [_ 1000000] (sub 5))))))

)