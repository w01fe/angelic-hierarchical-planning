(ns angelic.util.hybrid
;  (:use clojure.test  angelic.util  )
  (:require [angelic.util :as util]))
;            [angelic.util [propositions :as props] [intervals :as iv]]
;	    [clojure.contrib.generic.arithmetic :as ga]
; ;           [clojure.contrib.generic.comparison :as gc]
;            [clojure.contrib.generic.math-functions :as gm]))



;;; Helper types for expressions, assignments, and conditions

(defn split-var-maps [vars discrete-types numeric-types]
  (map (fn [vars] (into {} (map (fn [[t v]] [v t]) vars)))
	     (util/separate 
	      (fn [[t v]] 
		(cond (contains? discrete-types t) true
		      (contains? numeric-types t)  false
		      :else (throw (IllegalArgumentException.))))
	      vars)))

;; Helper

(defn check-hybrid-atom [atom arg-map var-types]
;  (println atom arg-map var-types)
  (let [args (util/safe-get arg-map (first atom))
	body (next atom)]
    (util/assert-is (= (count body) (count args)))
    (doseq [[v t] (map vector body args)]
      (util/assert-is (= t (get var-types v)) "%s %s %s" atom args var-types))
    (vec atom)))
