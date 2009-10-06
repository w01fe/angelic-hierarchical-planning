; This file provides utilities for caching functions of objects in their metadata.
; This provies functionality similar to memoization, but without leaking memory.

(ns edu.berkeley.ai.util.caches
  (:use clojure.test edu.berkeley.ai.util))

(defonce *unset-cache* (gensym "unset-cache"))

(defn add-caches [o & ks]
  (apply vary-meta o assoc (interleave ks (repeatedly #(atom *unset-cache*)))))

(defn invalidate-caches [o & ks]
  (doseq [k ks]
    (reset! (safe-get (meta o) k) *unset-cache*))
  o)

(defn set-cache [o k v]
  (reset! (safe-get (meta o) k) v)
  o)

(defn get-cache [o k]
  @(safe-get (meta o) k))

(defmacro cache 
  "Return the value set in key k of object o's metadata, or execute form,
   cache the value, and return it."
  [o k form]
  `(let [a# (safe-get (meta ~o) ~k)
	 cv# @a#]
     (if (identical? cv# *unset-cache*)
       (let [nv# ~form]
	 (reset! a# nv#)
	 nv#)
       cv#)))

(deftest test-caches
  (let [c (counter-from 0)
	o (add-caches {:a 1 :b 2} :c :d)]
    (is (= 0 (cache o :c (c))))
    (is (= 1 (cache o :d (c))))
    (is (= 0 (cache o :c (c))))
    (is (= 1 (cache o :d (c))))
    (is (= o {:a 1 :b 2}))
    (is (= (c) 2))
    (invalidate-caches o :c)
    (is (= 3 (cache o :c (c))))
    (is (= 1 (cache o :d (c))))
    (is (= (c) 4))
    (is (= 1 (get-cache o :d)))
    (set-cache o :d 5)
    (is (= 5 (get-cache o :d)))
    (is (= 5 (cache o :d 27)))
    (cache o :d (c))))