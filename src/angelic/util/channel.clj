(ns angelic.util.channel
  (:import [java.util ArrayList]))


(defrecord Channel [^ArrayList subscribers ^ArrayList publications])

(defn make-channel
  "A channel is a simple message abstraction that accepts publications
   and subscribers (callbacks), and guarantees that each subscriber
   is called exactly once for every publication, in order, including
   publications made before the subscription.  Not thread safe."
  [] (Channel. (ArrayList.) (ArrayList.)))

(defn publications [c] (doall (seq (:publications c))))

(defn publish!     [^Channel c pub]
  (.add ^ArrayList (:publications c) pub)
  (doseq [sub (doall (seq (:subscribers c)))] (sub pub)))

(defn subscribe!   [^Channel c sub]
  (.add ^ArrayList (:subscribers c) sub)
  (doseq [pub (doall (seq (:publications c)))] (sub pub)))


