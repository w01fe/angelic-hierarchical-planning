;; This file provides code to construct, modify, and solve (via external
;; solvers) linear programming problems.  

;; Variables are arbitrary objects, with .equals equality semantics. (?)

;; Linear combinations are represented as maps from vars to multipliers.

;; Objective is just a linear combination, to be *maximized*

;; Constraint set is map from linear combinations to interval vectors,
;; i.e. [nil 3] means c <= 3, [1 2] means 1 <= c <= 2.

;; Bounds is like constraints, but instead of LC have just vars.  Every
;; var must be mentioned.  Can map to nil for unbounded.


(ns edu.berkeley.ai.util.lp
  (:use clojure.test [edu.berkeley.ai.util :as util])
  (:import [java.util HashMap] [java.text DecimalFormat]))

(set! *warn-on-reflection* true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                               Basic Definitions    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-lp [bounds objective constraints]
  {:class ::LP 
   :constraints constraints
   :objective   objective
   :bounds      bounds})

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
   Returns [mps-file-string namer var-order]"
  [lp]
  (let [bounds      (:bounds lp)
	constraints (:constraints lp)
	objective   (:objective lp)
	namer       (make-mps-namer)
	out         (StringBuilder.)
	cols        (HashMap.)]
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
	
	(when (and (or l u) (not (= l u)))
	  (.append out 
		   (cond u         " UP "
			 :else     " PL "))
	  (.append out "BOUNDS1   ")
	  (.append out v-name)
	  (.append out "  ")
	  (when u (.append out (encode-mps-num u)))
	  (.append out "\n")))
       (println "Warning: skipping variable" v [l u] "which does not appear in obj or constraints.")))        

    (.append out "ENDATA\n")
    [(.toString out) namer (keys cols)]))

;; glpk gives us back
; n-rows n-cols
; stat stat rew   (stat = 1 for unsolvable, 2 for solvable ??)
; ROWS (bla bla bla)
; COLS (status val marginal?)

(defn cheap-sh [& args]
  (.waitFor (.exec (Runtime/getRuntime) #^"[Ljava.lang.String;" (into-array args))))

(defn solve-lp-glpk 
  "Solve the LP and return [var-binding-map sol-max-reward].  Returns nil for infeasible.
   Requrires GLPK (gnu LP solver kit) on the path."
  [lp]
  (let [[mps-file-data namer var-order] (lp->mps* lp)
	in-file (util/fresh-random-filename "/tmp/lp")
	out-file (str in-file ".out")]
    (util/spit in-file mps-file-data)
    (cheap-sh "glpsol" "--max" "-w" out-file "--mps" in-file)
    (let [[[rows cols] [stat1 stat2 rew] & body] (map #(read-string (str "[" % "]")) (util/read-lines out-file))]
      (cond (= stat1 stat2 1) nil ;infeasible
	    (= stat1 stat2 2) ; solved
	      [(into {} (map (fn [[status val marginal] var] [var val]) (drop rows body) var-order)) rew]
	    :else ;huh?
	      (throw (RuntimeException. (str "Unknown result statuses from glpk: " stat1 " "  stat2)))
	      ))))
      
	  
(defn solve-lp-clp
  "Solve the LP and return [var-binding-map sol-max-reward].  Returns nil for infeasible.
   Requrires CLP (COIN_OR LP solver) on the path."  
  [lp]
  (let [[mps-file-data namer var-order] (lp->mps* lp)
	in-file (util/fresh-random-filename "/tmp/lp")
	out-file (str in-file ".out")]
    (util/spit in-file mps-file-data)
    (cheap-sh "clp" "-max" "-import" in-file "-solve" "-solution" out-file)
    (let [[[status] [obj val rew] & body] (map #(read-string (str "[" % "]")) (util/read-lines out-file))]
      (assert (is (= [obj val] '[Objective value])))
      (cond ;(= stat1 stat2 1) nil ;infeasible
	    (= status 'optimal)
	      [(into {} (map (fn [[_ _ val _] var] [var val]) body var-order)) (- rew)]
	      ;; NOTE negation of reward due to apparent bug in CLP's handling of max.
	    :else ;huh?
	      (throw (RuntimeException. (str "Unknown result statuses from clp: " status)))
	      ))))

;; Calls for small LPs for both take about 40 ms. 


(def *wiki-lp* 
     (make-lp {:xone [nil 4] :ytwo [-1 1] :zthree nil} 
	      {:xone 1 :ytwo 4 :zthree 9} 
	      {{:xone 1 :ytwo 1} [nil 5] {:xone 1 :zthree 1} [10 nil] {:ytwo -1 :zthree 1} [7 7]}))
(def *wiki-lp-sol* [{:ytwo 1, :zthree 8, :xone 4} 80])
    
(deftest test-glpk
  (is (= (solve-lp-glpk *wiki-lp*) *wiki-lp-sol*)))

(deftest test-clp
  (is (= (solve-lp-clp *wiki-lp*) *wiki-lp-sol*)))

;; Wikipedia example
;; (println (lp->mps (make-lp {:xone [nil 4] :ytwo [-1 1] :zthree nil} {:xone 1 :ytwo 4 :zthree 9} {{:xone 1 :ytwo 1} [nil 5] {:xone 1 :zthree 1} [10 nil] {:ytwo -1 :zthree 1} [7 7]}))) 
     

(set! *warn-on-reflection* false)