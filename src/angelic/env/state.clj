(ns angelic.env.state
  (:require [angelic.util :as util]))

; Get-logger takes a precondition context.  Its equality semantics will be based
;; on values within this context, and changes outside this context. 
;; E.g., if context is var a, it doesn't matter if value was originally 2 or we set it to 2.
;;       but, for var b outside context, it does matter.
(defprotocol ContextualState
  (current-context [s])
  (extract-context [s c])
  (apply-effects   [s e])
  (get-logger      [s c-set])
  (equal-in-context [s os]))


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

(deftype LoggingFactoredState [init ^java.util.Set context puts ooc meta] 
  Object 
  (equals   [state lfs]
     (let [lfs ^LoggingFactoredState lfs]
       (and (= init (.init lfs)) (= context (.context lfs)) (= (ooc-effects state) (ooc-effects lfs)))))
   (hashCode [state]
     (unchecked-add (int (hash init))
       (unchecked-multiply (int 13) (int (hash (ooc-effects state))))))
  clojure.lang.IObj
   (meta [this] meta)
   (withMeta [this new-meta] (LoggingFactoredState. init context puts ooc new-meta))
  FactoredState
   (get-var [state var]
     (get-var init var))
   (set-var [state var val]
       (LoggingFactoredState. (set-var init var val) ; init
                              context
                              (assoc puts var val)
                              (if (.contains context var) ooc (assoc ooc var val))
                              {}))
   (set-vars [state vv-pairs]
       (LoggingFactoredState. (set-vars init vv-pairs)
                              context
                              (into puts vv-pairs)
                              (into ooc (remove #(.contains context (first %)) vv-pairs))
                              {}))
   (list-vars [state] (list-vars init))
   (as-map    [state] init)
  LoggingState
   (extract-effects [state]  puts)
   (ooc-effects     [state]  ooc)
  ContextualState 
   (current-context [state ]  context)
   (extract-context [state c] (fast-select-keys init c))
   (apply-effects   [state e] (set-vars state e))
   (get-logger      [state c] (make-logging-factored-state (as-map init) c))
   (equal-in-context [state other]
     (util/assert-is (= context (current-context other)))
     (every? identity (map #(= (get-var state %) (get-var other %)) context))))

(defn make-logging-factored-state [init-state context] 
  (LoggingFactoredState. init-state context {} {} {}))

(defn enforce-logger [state]
  (assert (instance? LoggingFactoredState state))
  state)


(def *m1* {:set-var assoc :set-vars into :get-var util/safe-get :list-vars keys :as-map identity})
(def *m2* {:current-context util/keyset :extract-context select-keys 
           :apply-effects into :get-logger make-logging-factored-state
           :equal-in-context =})

(extend clojure.lang.PersistentHashMap FactoredState *m1*  ContextualState *m2*)
(extend clojure.lang.PersistentArrayMap FactoredState *m1*  ContextualState *m2*)

(defn state-matches-map? [fs m]
  (every? (fn [[k v]] (= (get-var fs k) v)) m))


