;; This file provides code to construct, modify, and solve (via external
;; solvers) linear programming problems.  

;; Variables are arbitrary objects, with .equals equality semantics. (?)

;; Linear combinations are represented as maps from vars to multipliers.

;; Objective is just a linear combination, to be *maximized*

;; Constraint set is map from linear combinations to interval vectors,
;; i.e. [nil 3] means c <= 3, [1 2] means 1 <= c <= 2.

;; Bounds is like constraints, but instead of LC have just vars.  Every
;; var must be mentioned.  Can map to nil for unbounded.

;; Currently, we try to handle strict inequalities on a best-effort basis.
;; TODO: extend from bounds to constraints?

(ns edu.berkeley.ai.util.lp
  (:use clojure.test [edu.berkeley.ai.util :as util]
	[edu.berkeley.ai.util [linear-expressions :as le] [intervals :as iv] [caches :as caches]])
  (:import [java.util HashMap] [java.text DecimalFormat]))

(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                               Creating LP   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-lp [bounds objective constraints]
  {:class ::LP 
   :constraints constraints
   :objective   objective
   :bounds      bounds})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            MPS encoding of LP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn fix [obj size]
  (.substring (str obj "                                           ") 0 size)) 

(defn make-mps-namer
  "Make a function that maps from .equal objects to unique MPS names."
  [] {:forward (HashMap.) :backward (HashMap.) :count (atom 0)})

(defn obj->name [namer obj]
  (let [#^HashMap forward  (:forward namer)
	#^HashMap backward (:backward namer)
	count              (:count namer)]
    (or (.get forward obj)
      (let [n (swap! count inc)
	    name (.substring (str n "        ") 0 8)]
	(.put forward obj name)
	(.put backward name obj)
	name))))

(defn name->obj [namer name]
  (let [x (.get #^HashMap (:backward namer) name)]
    (when-not x (throw (RuntimeException. (str name " not a defined name in LP."))))
    x))

(def *mps-dec-format* (doto (DecimalFormat. "#.#######E0") (.setPositivePrefix "+")))
(defn encode-mps-num [n] 
  (let [s (.format #^DecimalFormat *mps-dec-format* (double n))]
    (assert (<= (.length s) 12))
    (.substring (str s "            ") 0 12)))
  

(defn lp->mps* 
  "Turn the lp into an MPS file string.
   Returns [mps-file-string namer var-order dummy-solutions]"
  [lp]
  (let [bounds      (:bounds lp)
	constraints (:constraints lp)
	objective   (:objective lp)
	namer       (make-mps-namer)
	out         (StringBuilder.)
	cols        (HashMap.)
	dummies     (HashMap.)]
    (.append out (str (fix "NAME" 14) "LP\n"))
    
    (.append out "ROWS\n")
    (.append out " N  REWARD  \n")
    (doseq [[var mul] objective]
      (.put cols var (cons (str "    " (obj->name namer var) "  REWARD    " (encode-mps-num mul) "\n") (.get cols var))))
    (doseq [[c [l u]] constraints]
      (let [c-name (obj->name namer c)]
	(doseq [[var mul] c]
	  (.put cols var (cons (str "    " (obj->name namer var) "  " c-name "  " (encode-mps-num mul) "\n") (.get cols var))))
	(.append out 
		 (cond (= l u)   " E  "
		       (and l u) " G  "
		       l         " G  "
		       u         " L  "
		       :else     " N  "))
	(.append out c-name)
	(.append out "\n")))
    
    (.append out "COLUMNS\n")
    (doseq [[var var-cols] cols
	    col var-cols]
      (when-not (contains? bounds var) (throw (RuntimeException. (str "Undefined variable " var))))
      (.append out #^String col))
    
    (.append out "RHS\n")
    (doseq [[c [l u]] constraints
	    :when (or l u)]
      (.append out "    RHS1      ")
      (.append out (obj->name namer c))
      (.append out "  ")
      (.append out (encode-mps-num (or l u)))
      (.append out "\n"))

    (.append out "RANGES\n")
    (doseq [[c [l u]] constraints
	    :when (and l u (not (= l u)))]
      (.append out "    RANGE1    ")
      (.append out (obj->name namer c))
      (.append out "  ")
      (.append out (encode-mps-num (- u l)))
      (.append out "\n"))      

    (.append out "BOUNDS\n")
    (doseq [[v [l u]] bounds]
      (if (or (.get cols v) (contains? objective v))
       (let [v-name (obj->name namer v)]
	(.append out 
		 (cond (not (or l u)) " FR "
		       (= l u)        " FX "
		       l              " LO "
		       :else          " MI "))
	(.append out "BOUNDS1   ")
	(.append out v-name)
	(.append out "  ")
	(when l (.append out (encode-mps-num l)))
	(.append out "\n")
	
	(when (and (or l u) (not (= l u)) u)  ;; CLP doesn't like PL.
	  (.append out 
		   (cond u         " UP "
			 :else     " PL "))
	  (.append out "BOUNDS1   ")
	  (.append out v-name)
	  (.append out "  ")
	  (when u (.append out (encode-mps-num u)))
	  (.append out "\n")))
       (do (println "Warning: skipping variable" v [l u] "which does not appear in obj or constraints.")
	   (.put dummies v (or l u 0)))
	   ))        

    (.append out "ENDATA\n")
    [(.toString out) namer (keys cols) dummies]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                     Solving LP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn cheap-sh [& args]
  (.waitFor (.exec (Runtime/getRuntime) #^"[Ljava.lang.String;" (into-array args))))

(defn solve-lp-glpk 
  "Solve the LP and return [var-binding-map sol-max-reward].  Returns nil for infeasible.
   Requrires GLPK (gnu LP solver kit) on the path."
  [lp]
  (let [[mps-file-data namer var-order dummies] (lp->mps* lp)
	in-file (util/fresh-random-filename "/tmp/lp")
	out-file (str in-file ".out")]
    (util/spit in-file mps-file-data)
    (cheap-sh "glpsol" "--max" "-w" out-file "--mps" in-file)
    (let [[[rows cols] [stat1 stat2 rew] & body] (map #(read-string (str "[" % "]")) (util/read-lines out-file))]
      (cond (= stat1 stat2 1) nil ;infeasible
	    (= stat1 stat2 2) ; solved
	      [(merge (into {} dummies)
		      (into {} (map (fn [[status val marginal] var] [var val]) (drop rows body) var-order)))
	       rew]
	    :else ;huh?
	      (throw (RuntimeException. (str "Unknown result statuses from glpk: " stat1 " "  stat2)))
	      ))))
      
	  
(def *bad-lp* nil)
(defn solve-lp-clp
  "Solve the LP and return [var-binding-map sol-max-reward].  Returns nil for infeasible.
   Requrires CLP (COIN_OR LP solver) on the path."  
  [lp]
  (let [[mps-file-data namer var-order dummies] (lp->mps* lp)
	in-file (util/fresh-random-filename "/tmp/lp")
	out-file (str in-file ".out")]
;    (println in-file)
    (util/spit in-file mps-file-data)
    (cheap-sh "clp" "-max" "-import" in-file "-solve" "-solution" out-file)
    (let [[[status] [obj val rew] & body] (map #(read-string (str "[" % "]")) (util/read-lines out-file))]
      (assert (is (= [obj val] '[Objective value])))
      (cond (= status 'infeasible) nil 
	    (= status 'optimal)
	      [(merge (into {} dummies)
		      (into {} (map (fn [[_ _ val _] var] [var val]) body var-order))) 
	       (- rew)]
	      ;; NOTE negation of reward due to apparent bug in CLP's handling of max.
	    :else ;huh?
	    (do  (println "Offending lp: " lp) (def *bad-lp* lp)
		 (throw (RuntimeException. (str "Unknown result statuses from clp: " status))))
	      ))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Calls for small LPs for both take about 40 ms. 

(def *wiki-lp* 
     (make-lp {:xone [nil 4] :ytwo [-1 1] :zthree nil} 
	      {:xone 1 :ytwo 4 :zthree 9} 
	      {{:xone 1 :ytwo 1} [nil 5] {:xone 1 :zthree 1} [10 nil] {:ytwo -1 :zthree 1} [7 7]}))
(def *wiki-lp-sol* [{:ytwo 1, :zthree 8, :xone 4} 80])

(def *another-lp*
     (make-lp {:x [0] :y [0] :z [0]}
	      {:x 1 :y 1 :z 2}
	      {{:y 1 :z 2} [nil 3]
	       {:x -1 :z 3} [nil 2]
	       {:x 2 :y 1 :z 1} [nil 1]}))

(def *another-lp-sol* [{:x 0 :y (/ 1.0 3) :z (/ 2.0 3)} (/ 5.0 3)])

(defn- approx-= [x y] (< (Math/abs (double (- x y))) 0.000001))
(defn- approx-=-maps [m1 m2]
  (and (= (set (keys m1)) (set (keys m2)))
       (every? #(apply approx-= %) (map #(vector (m1 %) (m2 %)) (keys m1)))))
(defn approx-=-lp-sols [[m1 r1] [m2 r2]]
  (and (approx-=-maps m1 m2) (approx-= r1 r2)))

(deftest test-glpk
  (is (approx-=-lp-sols (solve-lp-glpk *wiki-lp*) *wiki-lp-sol*))
  (is (approx-=-lp-sols (solve-lp-glpk *another-lp*) *another-lp-sol*)))

(deftest test-clp
  (is (approx-=-lp-sols (solve-lp-clp *wiki-lp*) *wiki-lp-sol*))
  (is (approx-=-lp-sols (solve-lp-clp *another-lp*) *another-lp-sol*)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                              Incremental LPs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An incremental LP always comes with a feasible solution, definitely optimal if cost is set.
;  Unsolvable LPs will be nil.

;; The only valid way to modify an incremental LP is to call make-incremental-lp*.  
;; Associng-on to it may render the metadata inconsistent.  

; TODO: normalize constraints somehow (i.e., lexicographically first var always = 1)

(derive ::IncrementalLP ::LP)

(defn make-incremental-lp* [bounds objective constraints solution cost]
  (doto (add-caches (assoc (make-lp bounds objective constraints) :class ::IncrementalLP) :solution :cost)
    (set-cache :solution solution)
    (set-cache :cost cost)))

(defn solve-incremental-lp [lp]
  (or (when (get-cache lp :cost) [(get-cache lp :solution) (get-cache lp :cost)])
      (print-debug 2 "Actually solving incremental lp...")
      (when-let [[sol cost] (solve-lp-clp lp)]
	(set-cache lp :solution sol)
	(set-cache lp :cost cost)
	[sol cost])))

(defn make-incremental-lp [bounds objective constraints]
  (let [lp (make-incremental-lp* bounds objective constraints nil nil)]
    (when (solve-incremental-lp lp)
      lp)))

(defn- current-feasible-solution [lp]
  (get-cache lp :solution))

(defn- current-optimal-cost [lp]
  (get-cache lp :cost))



(defn lp-interval-violation 
  "Return nil if no violation, or an interval with just the violated part."
  [[l u] v]
  (cond (< v (or l Double/NEGATIVE_INFINITY)) [l nil]
	(> v (or u Double/POSITIVE_INFINITY)) [nil u]
	:else nil))

(defn intersect-lp-intervals [[l1 u1] [l2 u2]]
  (let [l (cond (and l1 l2) (max l1 l2) l1 l1 l2 l2 :else nil)
	u (cond (and u1 u2) (min u1 u2) u1 u1 u2 u2 :else nil)]
    (when-not (and l u (> l u))
      [l u])))
							      
(defn lp-constraint-violation 
  "Return [c-map violated-i] or nil for no violation."
  [[c-map i] sol]
;  (println c-map i sol)
;  (println c-map i sol)
  (when-let [i (lp-interval-violation i (apply + (for [[v m] c-map] (* m (sol v)))))]
    [c-map i]))

(defn lp-constraints-violation
  "Return a constraint violation, or nil for all satisfied."
  [constraints sol]
  (some #(lp-constraint-violation % sol) constraints))

(defn lp-bounds-violation
  "Return [var violated-i] or nil for no violation"
  [bounds sol]
  (some (fn [[var val]] (lp-interval-violation (safe-get bounds var) val)) sol))

(defn lp-constraint-hessian 
  "Get the hessian [[a b ...] p] for an equality constraint. http://mathworld.wolfram.com/Plane.html"
  [[v-map rhs]]
  (let [den (sqrt (apply + (map #(* % %) (vals v-map))))]
    [(map-vals #(/ % den) v-map) (/ rhs den -1)]))

;; TODO: better projection; find feasible solution with simple matrix operation, or switch to Octave/Matlab/R.
(defn lp-constraint-projection 
  "Project the solution onto the given equality constraint."
  [constraint sol]
  (let [[norm p] (lp-constraint-hessian constraint)
	dist     (+ p (apply + (map #(* (norm %) (sol %)) (keys norm))))]
    (reduce (fn [sol [k v]] (assoc sol k (- (sol k) (* dist v)))) sol norm)))

;; TODO: factor out assigned variables?
(defn adjust-lp-var-bounds [lp var new-bounds strict?]
  (let [old-bounds   (safe-get (:bounds lp) var)
	final-bounds (intersect-lp-intervals old-bounds new-bounds)]
    (if (or (not final-bounds)
	    (and strict? (let [[l u] final-bounds [nl nu] new-bounds] 
                           (and l u (or nl nu) (= l u (or nl nu)))))) 
        (print-debug 2 "New bounds for" var "are inconsistent."
                     ;lp ^lp var new-bounds old-bounds final-bounds strict?
                     ) 
      (let [sol          (current-feasible-solution lp)
	    cur-val      (safe-get sol var)
	    [l-v u-v]    (lp-interval-violation final-bounds cur-val)	    new-bounds   (assoc (:bounds lp) var final-bounds)]
	(if (not (or l-v u-v)) 
	    (do (print-debug 2 "Solution within new bounds!") 
		(make-incremental-lp* new-bounds (:objective lp) (:constraints lp) sol (current-optimal-cost lp)))
	  (let [new-sol (assoc sol var (or l-v u-v))]
	    (if (not (lp-constraints-violation (:constraints lp) new-sol))
	        (do (print-debug 2 "Solution fixed by projecting to new bounds.")
		    (make-incremental-lp* new-bounds (:objective lp) (:constraints lp) new-sol 
					  (if (= 0 (get (:objective lp) var 0)) (current-optimal-cost lp) nil)))
	      (do (print-debug 2 "All else failed with new bounds; solving again from scratch.")
		  (make-incremental-lp new-bounds (:objective lp) (:constraints lp)) ))))))))
			      

(defn adjust-lp-constraint-bounds [lp constraint new-bounds]
  (let [old-bounds (get (:constraints lp) constraint)
	merged-bounds (intersect-lp-intervals old-bounds new-bounds)
	computed-bounds (when merged-bounds (iv/unparse-interval
					     (le/evaluate-linear-expr-ga 
					      #(iv/parse-interval (safe-get (:bounds lp) %))
					      constraint)))
	final-bounds (when merged-bounds (intersect-lp-intervals (intersect-lp-intervals old-bounds new-bounds) computed-bounds))]
    (print-debug 3  "For" constraint "have old bounds" old-bounds "new" new-bounds
	     "computed" computed-bounds)
    (if (not final-bounds) (print-debug 2 "New bounds for constraint are inconsistent.")
      (let [new-constraints (assoc (:constraints lp) constraint final-bounds)
	    sol (current-feasible-solution lp)]
	(if-let [[vc [vl vh]] (lp-constraint-violation [constraint final-bounds] sol)]
	    (or (print-debug 2 "current lp infeasible with new constraint.")
		(and (not (apply = final-bounds))
		     (let [epsilon 0.00000000001
			   target (if vl (+ vl epsilon) (- vh epsilon))
			   proj (lp-constraint-projection [constraint target] sol)]
		       (and (not (lp-constraints-violation (:constraints lp) proj))
			    (not (lp-bounds-violation (:bounds lp) proj))
			    (do (print-debug 2 "Projecting fixed it.")
				(make-incremental-lp* (:bounds lp) (:objective lp) new-constraints
						     proj nil)))))
		(do (print-debug 2 "Projecting failed, or not attempted for eq; trying from scratch")
		    (make-incremental-lp (:bounds lp) (:objective lp) new-constraints)))
	  (do (print-debug 2 "lucky; still feasible with new constraint")
	      (make-incremental-lp* (:bounds lp) (:objective lp) new-constraints sol (current-optimal-cost lp))))))))  


;; TODO: smarter handling of some things with constraints, i.e., free variables.?
(defn add-lp-constraint 
  "Add a new constraint, specified as [linear-expr-map [lb ub]] to the LP.  The constraint should
   be <=, =, or >=, but not multiple (i.e., if both lb and ub are provided, they should be equal.
   Ideally, linear-expr-map should be normalized."  
  [lp [constraint-lm new-bounds] strict?]
  (assert (isa? (:class lp) ::IncrementalLP))
  (if (== (count constraint-lm) 1)
      (let [[var wt] (first constraint-lm)]
	(cond (== wt 1) (adjust-lp-var-bounds lp var new-bounds strict?)
	      (>= wt 0) (adjust-lp-var-bounds lp var (map #(when % (/ % wt)) new-bounds) strict?)
	      (< wt 0)  (let [[l u] new-bounds] 
			  (adjust-lp-var-bounds lp var (map #(when % (/ % wt)) [u l]) strict?))))
    (adjust-lp-constraint-bounds lp constraint-lm new-bounds)))


;; TODO: idea here with dir is to supply an optimal initial value for the variable.
(defn add-lp-var [lp var [l u] dir]
  (when (and l u) (assert (<= l u)))
  (if (contains? (:bounds lp) var) 
      (if (or l u) 
          (throw (RuntimeException. (str "Duplicate LP var, new bounds; not implemented yet.")))
        lp)
    (make-incremental-lp* (assoc (:bounds lp) var [l u]) (:objective lp) (:constraints lp)
                          (assoc (current-feasible-solution lp) var ;(or l u 0)
                                 (cond (or (not dir) (zero? dir)) (or l u 0)
                                       (pos? dir) (or u 100000000)
                                       (neg? dir) (or l -100000000)))
                          (current-optimal-cost lp))))

(defn- pegged? 
  "Is this variable already pegged against its bound in the provided direction (i.e., the direction 
   it appears in the objective function?)"
  [lp var val dir]
  (cond (or (not dir) (zero? dir)) true
        (pos? dir) (= val (second (safe-get (:bounds lp) var)))
	(neg? dir) (= val (first (safe-get (:bounds lp) var)))))

(defn increment-lp-objective [lp v-map]
  "Increment the objective of the LP; v-map is a linear expression, which may include abs. 
   value terms (which must appear negatively)."
;  (println lp v-map "\n\n\n")
  (if (some map? (keys v-map))  ; Get rid of absolute value terms.
      (apply increment-lp-objective 
        (reduce (fn [[lp v-map] k]
                  (let [dummy-var (gensym "abs-var")
                        val       (get v-map k)
                        const     (- (get k nil 0))
                        k2         (dissoc k nil)]
                    (assert (< val 0))
                    [(add-lp-constraint
                      (add-lp-constraint 
                       (add-lp-var lp dummy-var [0 nil] +1)
                       [(assoc k2 dummy-var -1) [nil const]] false)
                      [(assoc k2 dummy-var 1) [const nil]] false)
                     (assoc (dissoc v-map k) dummy-var val)]))
                [lp v-map]
                (filter map? (keys v-map))))
    (let [sol (current-feasible-solution lp)
          cost (current-optimal-cost lp)]
      (make-incremental-lp* 
       (:bounds lp) (merge-with + (:objective lp) v-map) (:constraints lp)
       sol			
       (when (and cost (every? (fn [[var val]] (pegged? lp var (safe-get sol var) val)) v-map))
         (print-debug 2 "Got pegged solution when incrementing objective!")
         (apply + cost (map (fn [[var val]] (* val (safe-get sol var))) v-map)))))))


(deftest test-incremental-lp ;TODO: improve
  (let [lp1 (-> (make-incremental-lp {} {} {}) (add-lp-var :bam nil nil) (add-lp-constraint [{:bam 1} [-1 nil]] false) (add-lp-constraint [{:bam -1} [-1 nil]] false) (add-lp-var :boo [-1 1] nil))]
    (is (= lp1 {:class ::IncrementalLP, :constraints {}, :objective {}, :bounds {:boo [-1 1], :bam [-1 1]}}))
    (is (= (current-feasible-solution lp1)  {:boo -1, :bam 0}))
    (is (= (current-optimal-cost lp1) 0)))
  (is (= (:constraints (-> (make-incremental-lp {} {} {}) (add-lp-var :bam nil nil) (add-lp-constraint [{:bam 1} [-1 nil]] false) (add-lp-constraint [{:bam -1} [-1 nil]] false) (add-lp-var :boo [-1 1] nil) (add-lp-constraint [{:bam 1 :boo 1} [-3 4]] false) (add-lp-constraint (linear-expr-lez->normalized-inequality {:bam -1 :boo -1 nil 1} false) false)))
	 {{:bam 1, :boo 1} [1 2]}))
  
  ;; Test absolute value.
  (is (= (second (solve-incremental-lp 
                  (increment-lp-objective 
                   (make-incremental-lp {:x [-3 2]} {:x 0.5 } {}) 
                    {{:x 1} -1})))
         0))

  (is (= (second (solve-incremental-lp 
                  (increment-lp-objective 
                   (make-incremental-lp {:x [-3 2]} {:x -2} {}) 
                    {{:x 1} -1})))
         3))

  (is (= (second (solve-incremental-lp 
                  (increment-lp-objective 
                   (make-incremental-lp {:x [-3 2]} {:x 2} {}) 
                    {{:x 1} -1})))
         2))

  (is (= (second (solve-incremental-lp 
                  (increment-lp-objective 
                   (make-incremental-lp {:x [-3 2]} {:x 1} {}) 
                    {{:x 1 nil 2} -2})))
         -2))
  )



; max -|y|:
; max -x s.t.
; x >= y, x >= -y 
; max -x s.t. 
; |y| > x
; y > x


     

(set! *warn-on-reflection* false)