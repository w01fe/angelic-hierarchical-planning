(ns angelic.hierarchy.state-set
  (:refer-clojure :exclude [empty?])
  (:require [edu.berkeley.ai.util :as util]
            [clojure.contrib.combinatorics :as combos]
            [angelic.env.state :as state]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Implicit Set Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol ImplicitStateSet
  (empty?    [s] "Is this set empty")
;  (singleton-val [s v] "Return single possible value for far, or nil if not singleton")
  (singleton [s] "Return the singleton element making up this set, or nil if cardinality != 1.")
  (some-element [s] "Return an arbitrary element of this set, or throw if empty. ")
  (explicit-set [s] "Return an explicit outcome set. ")
  (constrain [ss constraint] "Apply a constraint."))


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

;(def no-effect ::no-effect)

(declare make-logging-factored-state-set)

(declare extract-logging-state)

(deftype LoggingFactoredStateSet [init #^java.util.Set context puts ooc meta] 
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

  ImplicitStateSet
   (empty? [ss] #_(println "AAA" init) (some clojure.core/empty? (vals init)))
   (singleton [ss] 
     (when (every? util/singleton? (vals init))
       (extract-logging-state ss (util/map-vals util/safe-singleton init))))
   (some-element [ss]
     (assert (not (empty? ss)))
     (extract-logging-state ss (util/map-vals first init)))
   (explicit-set [ss]
     (let [kvs (seq init)
           ks  (map key kvs)
           vss (map val kvs)]
       (set (for [vs (apply combos/cartesian-product vss)] (extract-logging-state ss (zipmap ks vs))))))
   (constrain    [ss constraint] 
     (assert (every? context (keys constraint)))     
     (state/set-vars ss
      (for [[var vals] constraint] [var (clojure.set/intersection vals (state/get-var ss var))])))
   
  state/FactoredState
   (get-var [ss var]
     (let [x (state/get-var init var)]
       (util/assert-is (set? x) "%s" [var])
       x))
   
   (set-var [ss var val]
       (util/assert-is (set? val) "%s" [var])
       (LoggingFactoredStateSet. (state/set-var init var val) ; init
                              context
                              (assoc puts var val)
                              (if (.contains context var) ooc (assoc ooc var val))
                              {}))
   (set-vars [ss vv-pairs]
       (doseq [[var val] vv-pairs] (util/assert-is (set? val) "%s" [var]))
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
  (every? #(util/singleton? (state/get-var ss %)) vars))

(defn get-known-var [ss var] (util/safe-singleton (state/get-var ss var)))

(defn ss-str [ss] "LFSS" (print-str (dissoc (state/as-map ss) :const)))
(defmethod print-method LoggingFactoredStateSet [ss o] (print-method (ss-str ss) o))

(defn proper-subset? [ss1 ss2]
  (let [m1 (state/as-map ss1)
        m2 (state/as-map ss2)
        ks (util/keyset m1)]
    (assert (= ks (util/keyset m2)))
    (and (every? #(util/subset? (m1 %) (m2 %)) ks)
         (some   #(util/proper-subset? (m1 % ) (m2 %)) ks))
    #_ (or 
        
        (println (filter #(not (clojure.set/subset? (nth % 1) (nth % 2))) (map #(vector % (m1 %) (m2 %)) ks))
                 (filter   #(util/proper-subset? (m1 % ) (m2 %)) ks)
                 ))))


