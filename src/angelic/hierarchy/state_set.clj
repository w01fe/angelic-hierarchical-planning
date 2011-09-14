(ns angelic.hierarchy.state-set
  (:refer-clojure :exclude [empty?])
  (:require [angelic.util :as util]
            [clojure.contrib.combinatorics :as combos]
            [angelic.env.util :as env-util]            
            [angelic.env.state :as state]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implicit Set Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Protocol used to represent both state sets, and value sets.
;; State sets are like states, where the values implement PSet.
;; Should also implement proper equality
(defprotocol PSet
  (empty?    [s] "Is this set empty")
  (singleton [s] "Return the singleton element making up this set, or nil if cardinality != 1.")
  (some-element [s] "Return an arbitrary element of this set, or throw if empty. ")
  (explicit-set [s] "Return an explicit outcome set. ")
  (constrain [ss constraint] "Apply a constraint.")
  (as-constraint [ss] "Return a constraint view.")
  (subset? [s1 s2] "Is this set a (possibly improper) subset of the other?"))

;; Allow Clojure sets to be used as value sets.
(extend-type clojure.lang.IPersistentSet
  PSet
  (empty? [s] (clojure.core/empty? s))
  (singleton [s] (util/singleton s))
  (some-element [s]
    (assert (not (clojure.core/empty? s)))
    (first s))
  (explicit-set [s] s)
  (constrain [s constraint]
    (assert (set? constraint))
    (clojure.set/intersection s constraint))
  (as-constraint [s] s)
  (subset? [s1 s2] (util/subset? s1 s2)))


(defn assert-pset! [x]
  nil #_ (assert (satisfies? PSet x)))

(defn proper-subset? [s1 s2]
  (and (subset? s1 s2) (not (= s1 s2))))

(defn safe-singleton [s] (let [x (singleton s)] (assert x) x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; Factored Implicit Sets ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here, we assume independent, set-valued effects and
; set-valued constraints (map from var to set of effect vals).
; For now, we abuse the interfaces form ordinary states, simply changing the 
; semantics so values are now sets of admissible values. 

;; TODO:Note: we have to be really careful about OOC-effects here.
;; for now, we can just require that these be unconditional.
;; If we add unions, etc later, worry about details.
;; TODO: constraint is not the same as set-vars ?  ???

(declare make-logging-factored-state-set)

(declare extract-logging-state)

;; To work around bug in c-c version for now.
(defn cartesian-product
  "All the ways to take one item from each sequence"
  [& seqs]
  (let [v-original-seqs (vec seqs)
        step
        (fn step [v-seqs]
          (let [increment
                (fn [v-seqs]
                  (loop [i (dec (count v-seqs)), v-seqs v-seqs]
                    (if (= i -1) nil
                        (if-let [rst (next (v-seqs i))]
                          (assoc v-seqs i rst)
                          (recur (dec i) (assoc v-seqs i (v-original-seqs i)))))))]
            (when v-seqs
              (cons (map first v-seqs)
                    (lazy-seq (step (increment v-seqs)))))))]
    (when (every? seq seqs)
      (lazy-seq (step v-original-seqs)))))

(deftype LoggingFactoredStateSet [init ^java.util.Set context puts ooc meta] 
  Object 
  (equals   [ss lfs]
     (let [lfs ^LoggingFactoredStateSet lfs]
       (and (= init (.init lfs)) (= context (.context lfs)) (= (state/ooc-effects ss) (state/ooc-effects lfs)))))
   (hashCode [ss]
     (unchecked-add (int (hash init))
       (unchecked-multiply (int 13) (int (hash (state/ooc-effects ss))))))

  clojure.lang.IObj
   (meta [this] meta)
   (withMeta [this new-meta] (LoggingFactoredStateSet. init context puts ooc new-meta))

  PSet
   (empty? [ss]  (some empty? (vals init)))
   (singleton [ss]
     (when (every? util/singleton? (vals init))
       (extract-logging-state ss (zipmap (keys init) (map first (vals init))))))
   (some-element [ss]
     (extract-logging-state ss (util/map-vals some-element init)))
   (explicit-set [ss]
     (let [ks  (keys init)
           vss (map explicit-set (vals init))]
       (set (for [vs (apply cartesian-product vss)] (extract-logging-state ss (zipmap ks vs))))))
   (constrain    [ss constraint] 
     (state/set-vars ss
      (for [[var vals] constraint
            :let [cur-vals (state/get-var ss var)
                  isect    (constrain cur-vals vals)]
            :when (not (= (count isect) (count cur-vals)))]
        [var isect])))
  ;   (util/assert-is (contains? context var)) ;; TODO: can't actually assert this without stronger conditions on what must be reported in precondition contexts, unfortunately.  I.e., how to do it may not depend on initial value, but operation may still constrain it ?!
   ;; Note difficulties: must capture all of context (even unset parts), plus set parts of non-context.
   ;; If too large, can mess up SA.
   (as-constraint [ss] 
      (util/map-vals as-constraint (into (state/extract-context ss (state/current-context ss)) (state/ooc-effects ss))))
   (subset? [ss1 ss2]
     (let [m1 (state/as-map ss1)
           m2 (state/as-map ss2)
           ks (util/keyset m1)]
       (assert (= ks (util/keyset m2)))
       (every? #(subset? (m1 %) (m2 %)) ks)))

   
  state/FactoredState
   (get-var [ss var]
     (let [x (state/get-var init var)]
       (assert-pset! x)
       x))
   
   (set-var [ss var val]
       (assert-pset! val)
       (LoggingFactoredStateSet. (state/set-var init var val) ; init
                              context
                              (assoc puts var val)
                              (if (.contains context var) ooc (assoc ooc var val))
                              {}))
   (set-vars [ss vv-pairs]
       (doseq [[var val] vv-pairs] (assert-pset! val))
       (LoggingFactoredStateSet. (state/set-vars init vv-pairs)
                              context
                              (into puts vv-pairs)
                              (into ooc (remove #(.contains context (first %)) vv-pairs))
                              {}))
   (list-vars [ss] (state/list-vars init))
   (as-map    [ss] init)

  state/LoggingState
   (extract-effects [ss]  puts)
   (ooc-effects     [ss]  ooc)

  state/ContextualState 
   (current-context [ss ]  context)
   (extract-context [ss c] (state/fast-select-keys init c))
   (apply-effects   [ss e] (state/set-vars ss e))
   (get-logger      [ss c] (LoggingFactoredStateSet. (state/as-map init) c {} {} {})))

(defn extract-logging-state [^LoggingFactoredStateSet ss concrete-map]
  (angelic.env.state.LoggingFactoredState.
   concrete-map
   (.context ss)
   (state/fast-select-keys concrete-map (keys (state/extract-effects ss)))
   (state/fast-select-keys concrete-map (keys (state/ooc-effects ss)))   
   (meta ss)))


(def empty-lfss (LoggingFactoredStateSet. {:dummy #{}} #{:dummy} {} {} {}))


(defn make-logging-factored-state-set [lfss]
  (assert (apply = (map state/current-context lfss)))
  (assert (apply = (map (comp keys state/ooc-effects) lfss)))  
  (assert (apply = (map meta lfss)))  
  (if (clojure.core/empty? lfss) empty-lfss
      (let [effect-vars (set (apply concat (map (comp keys state/extract-effects) lfss)))
            ooc-vars    (set (apply concat (map (comp keys state/ooc-effects) lfss)))
            implicit-ss (into {} (for [v (state/list-vars (first lfss))]
                                   [v (set (map #(state/get-var % v) lfss))]))]
        (LoggingFactoredStateSet.
         implicit-ss
         (state/current-context (first lfss))
         (state/fast-select-keys implicit-ss effect-vars)
         (state/fast-select-keys implicit-ss ooc-vars)
         (meta (first lfss))))))

(defn vars-known? [ss vars]
  (every? #(singleton (state/get-var ss %)) vars))

(defn get-known-var [ss var] (util/make-safe (singleton (state/get-var ss var))))

(defn ss-str [ss] "LFSS" (print-str (dissoc (state/as-map ss) :const)))
(defmethod print-method LoggingFactoredStateSet [ss o] (print-method (ss-str ss) o))





(defn initial-logging-ss [env]
  (make-logging-factored-state-set [(env-util/initial-logging-state env)]))