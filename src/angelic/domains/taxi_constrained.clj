(ns angelic.domains.taxi-constrained
  (:require [angelic.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]
            [angelic.sas :as sas]
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))


(defn- make-left   [t cx]
  (env-util/make-factored-primitive ['left t cx]  {['atx t] cx} {['atx t] (dec cx)} -1))

(defn- make-right  [t cx]
  (env-util/make-factored-primitive ['right t cx] {['atx t] cx} {['atx t] (inc cx)} -1))

(defn- make-down  [t cy]
  (env-util/make-factored-primitive ['down t cy]  {['aty t] cy} {['aty t] (dec cy)} -1))

(defn- make-up    [t cy]
  (env-util/make-factored-primitive ['up t cy] {['aty t] cy} {['aty t] (inc cy)} -1))

(defn- make-pickup  [pass taxi [x y]]
  (env-util/make-factored-primitive 
   ['pickup pass taxi x y] 
   {['atx taxi]        x     ['aty taxi]        y
    ['passat pass] [x y]}
   {['passat pass] taxi}
   -1))

(defn- make-dropoff [pass taxi [x y]]
  (env-util/make-factored-primitive 
   ['dropoff pass taxi x y] 
   {['atx taxi]        x     ['aty taxi] y 
    ['passat pass] taxi}
   {['passat pass] [x y]}
   -1))


;; Taxis are [name init-pos]
;; Passengers are [name spos gpos taxis]
(defn make-constrained-taxi-env [width height passengers taxis constrain-dropoff?]
  (let [xs    (set (range 1 (inc width)))
        ys    (set (range 1 (inc height)))
        locs  (set (for [x xs, y ys] [x y]))]
    (sas/make-sas-problem
     (into {sas/goal-var-name sas/goal-var}
           (concat
            (for [[pass _ _ pts] passengers] [['passat pass] (sas/make-sas-var ['passat pass]
                                                                       (apply conj locs pts))])
            (for [[taxi] taxis]      [['atx taxi] (sas/make-sas-var ['atx taxi] xs)])
            (for [[taxi] taxis]      [['aty taxi] (sas/make-sas-var ['aty taxi] ys)])))
     (into {sas/goal-var-name sas/goal-false-val}
           (concat
            (for [[pass s] passengers] [['passat pass] s])
            (for [[taxi [sx _]] taxis] [['atx taxi] sx])
            (for [[taxi [_ sy]] taxis] [['aty taxi] sy])))
     (cons
      (env-util/make-factored-primitive
       [:goal]
       (into {sas/goal-var-name sas/goal-false-val}
             (for [[pass _ d] passengers] [['passat pass] d]))     
       {sas/goal-var-name sas/goal-true-val}
       0)
      (concat
       (for [[taxi] taxis, x (range 2 (inc width))] (make-left taxi x))
       (for [[taxi] taxis, x (range 1 width)]       (make-right taxi x))
       (for [[taxi] taxis, y (range 2 (inc height))] (make-down taxi y))
       (for [[taxi] taxis, y (range 1 height)]       (make-up   taxi y))
       (for [[pass _ _ pts] passengers, taxi pts, x xs, y ys] (make-pickup pass taxi [x y]))
       (if constrain-dropoff?
         (for [[pass _ dest pts] passengers, taxi pts] (make-dropoff pass taxi dest))
         (for [[pass _ _ pts] passengers, taxi pts, x xs, y ys] (make-dropoff pass taxi [x y]))))))))


(defn next-random-loc
  ([^Random r width height]
     [(inc (.nextInt r (int width))) (inc (.nextInt r (int height)))])
  ([^Random r width height blackset]
     (let [n (next-random-loc r width height)]
       (if (contains? blackset n)
         (recur r width height blackset)
         n))))



(defn make-random-taxi-env [width height passenger-taxis constrain-dropoff? seed]
  (let [r     (Random. seed)
        taxis (apply clojure.set/union (map second passenger-taxis))]
    (.nextDouble r) (.nextDouble r)
    (make-constrained-taxi-env
     width height
     (for [[p ts] passenger-taxis
           :let [from (next-random-loc r width height)]]
       [p from (next-random-loc r width height #{from}) ts])
     (for [t taxis] [t (next-random-loc r width height)])
     constrain-dropoff?)))


(defn make-random-independent-taxi-env [width height n-passengers constrain-dropoff? seed]
  (make-random-taxi-env width height (for [i (range n-passengers)] [i #{i}]) constrain-dropoff? seed))

(defn make-random-pairwise-taxi-env [width height n-passengers constrain-dropoff?  seed]
  (make-random-taxi-env width height (if (= n-passengers 1) [[0 #{0}]] (for [i (range n-passengers)] [i #{i (mod (inc i) n-passengers)}])) constrain-dropoff? seed))

(defn make-random-single-taxi-env [width height n-passengers constrain-dropoff? seed]
  (make-random-taxi-env width height (for [i (range n-passengers)] [i #{0}]) constrain-dropoff? seed))
