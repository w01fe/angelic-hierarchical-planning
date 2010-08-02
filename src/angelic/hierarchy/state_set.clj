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
  (singleton [s] "Return the singleton element making up this set, or nil if cardinality != 1")
  (explicit-set [s] "Return an explicit outcome set")
  (constrain [ss constraint] "Apply a constraint."))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; Factored Implicit Sets ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here, we assume independent, set-valued effects and
; set-valued constraints (map from var to set of effect vals).
; For now, we abuse the interfaces form ordinary states, simply changing the 
; semantics so values are now sets of admissible values. 

(declare make-logging-factored-state-set)

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
   (empty? [ss] (some clojure.core/empty? (vals init)))
   (singleton [ss] 
     (when (every? util/singleton? (vals init))
       (util/map-vals util/safe-singleton init)))
   (explicit-set [ss]
     (let [kvs (seq init)
           ks  (map key kvs)
           vss (map val kvs)]
       (set (for [vs (apply combos/cartesian-product vss)] (zipmap ks vs)))))
   (constrain    [ss constraint] 
     (assert (every? context (keys constraint)))     
     (state/set-vars ss
      (for [[var vals] constraint] [var (clojure.set/intersection vals (state/get-var ss var))])))
   
  state/FactoredState
   (get-var [ss var]
     (state/get-var init var))
   (set-var [ss var val]
       (LoggingFactoredStateSet. (state/set-var init var val) ; init
                              context
                              (assoc puts var val)
                              (if (.contains context var) ooc (assoc ooc var val))
                              {}))
   (set-vars [ss vv-pairs]
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

(defn make-singleton-logging-factored-state-set
  ([init-state] (make-singleton-logging-factored-state-set init-state (util/to-set (state/list-vars init-state))))
  ([init-state context] (LoggingFactoredStateSet. (util/map-vals (fn [x] #{x}) init-state) context {} {} {})))


