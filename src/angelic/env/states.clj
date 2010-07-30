(ns w01fe.env.states
  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util])
  (:import [java.util Set Map])
  )

; Get-logger takes a precondition context.  Its equality semantics will be based
;; on values within this context, and changes outside this context. 
;; E.g., if context is var a, it doesn't matter if value was originally 2 or we set it to 2.
;;       but, for var b outside context, it does matter.
(defprotocol ContextualState
  (current-context [s])
  (extract-context [s c])
  (apply-effects   [s e])
  (get-logger      [s c-set]))


(defprotocol LoggingState
  (ooc-effects     [s])  ; Return just out-of-context effects.
  (extract-effects [s]))

(defn transfer-effects [target-state child] (apply-effects target-state (extract-effects child)))

(defprotocol FactoredState
  (set-var   [state var val])
  (set-vars  [state vv-pairs])
  (get-var   [state var])
  (list-vars [state])
  (as-map    [state]))

(defn get-vars [state vars]
  (into {} (for [v vars] [v (get-var state v)])))

;; TODO: use dissoc in some cases?
(defn fast-select-keys [map key-set]
  (let [mc (count map) kc (count key-set)]
    (assert (<= kc mc))
    (if (= mc kc) map
      (persistent! (reduce #(assoc! %1 %2 (get map %2)) (transient {}) key-set)))))

(declare make-logging-factored-state)

(deftype LoggingFactoredState [init #^Set context] :as state
  Object 
   (equals    [lfs]
     (and (= init (:init lfs)) (= context (:context lfs)) (= (ooc-effects state) (ooc-effects lfs))))
   (hashCode []
     (unchecked-add (int (hash init))
       (unchecked-multiply (int 13) (int (hash (ooc-effects state))))))
  FactoredState
   (get-var [var]
     (get-var init var))
   (set-var [var val]
     (let [old-meta (meta state)]
       (LoggingFactoredState. (set-var init var val) ; init
                              context
                              {:puts (assoc (:puts old-meta) var val)
                               :ooc  (if (.contains context var) (:ooc old-meta) (assoc (:ooc old-meta) var val))}
                              {})))
   (set-vars [vv-pairs]
     (let [old-meta (meta state)]
       (LoggingFactoredState. (set-vars init vv-pairs)
                              context
                              {:puts (into (:puts old-meta) vv-pairs)
                               :ooc  (into (:ooc old-meta) (remove #(.contains context (first %)) vv-pairs))}
                              {})))
   (list-vars [] (list-vars init))
   (as-map [] init)
  LoggingState
   (extract-effects []  (util/safe-get (meta state) :puts))
   (ooc-effects     []  (util/safe-get (meta state) :ooc) #_(util/filter-map #(not (.contains context (key %))) (util/safe-get (meta state) :puts)))
  ContextualState 
   (current-context []  context)
   (extract-context [c] (fast-select-keys init c))
   (apply-effects   [e] (set-vars state e))
   (get-logger      [c] (make-logging-factored-state (as-map init) c)))

(defn make-logging-factored-state [init-state context] 
  (LoggingFactoredState init-state context {:puts {} :ooc {}} {}))

(defn enforce-logger [state]
  (assert (= (type state) ::LoggingFactoredState))
  state)


(def *m1* {:set-var assoc :set-vars into :get-var util/safe-get :list-vars keys :as-map identity})
(def *m2* {:current-context util/keyset :extract-context select-keys 
                   :apply-effects into :get-logger make-logging-factored-state})

(extend clojure.lang.PersistentHashMap FactoredState *m1*  ContextualState *m2*)
(extend clojure.lang.PersistentArrayMap FactoredState *m1*  ContextualState *m2*)

;(def *m3* {:set-var assoc! :get-var util/safe-get :list-vars keys :as-map persistent!})
;(extend clojure.lang.PersistentHashMap$TransientHashMap
;  FactoredState *m3* ContextualState *m2*)
;(extend clojure.lang.PersistentArrayMap$TransientArrayMap
;  FactoredState *m3* ContextualState *m2*)

(defn state-matches-map? [fs m]
  (every? (fn [[k v]] (= (get-var fs k) v)) m))


(deftest test-logging-factored-state
  (let [si {:a 1 :b 2 :c 3}
        s1 (get-logger si #{:a})
        s2 (set-var s1 :a 1)
        s3 (set-var s1 :b 2)
        s4 (set-var (set-var s1 :a 1) :b 2)
        s5 (set-var (set-var s1 :a 1) :c 4)
        ss [s1 s2 s3 s4 s5]
        equal-sets [#{0 1} #{2 3} #{4}]
        ]
    (is (= (map as-map          ss) [si si si si (assoc si :c 4)]))
    (is (= (map extract-effects ss) [{} {:a 1} {:b 2} {:a 1 :b 2} {:a 1 :c 4}]))
    (is (= (map ooc-effects     ss) [{} {} {:b 2} {:b 2} {:c 4}]))
    (doseq [es equal-sets] 
      (is (apply = (map ss es)))
      (is (apply = (map (comp hash ss) es))))
    (doseq [[s1 s2] (util/combinations equal-sets 2), i1 s1, i2 s2]
      (is (not (= i1 i2)))
      (is (not (= (hash i1) (hash i2)))))))

;; TODO: make method so we can use transients?



;(defn get-logging-state-gets [s] @(:gets (meta s)))
;(defn get-logging-state-puts [s] (util/safe-get (meta s) :puts))



