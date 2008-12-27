;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.actions.clj
;;
;;  Exports for states. 

(in-ns 'edu.berkeley.angel.search)

(defstruct action :class :name :fn)

(defn make-action "function is a fn from states to [state reward] pairs.  "
  [name next-fn]
  (struct action ::Action name next-fn))

(defn next-state [state action]
  (let [[next reward] ((:fn action) state)]
    (with-meta next
      {:act-seq (conj (:act-seq ^state) action)
       :reward (+ reward (:reward ^state))})))

       
(defstruct action-space :class :fn)

(defn make-action-space "function is a map from states to lazy seq of action objects"
  [fn]
  (struct action-space ::ActionSpace fn))

(defmulti applicable-actions #(vector (:class %1) (:class %2)))
 
(defmethod applicable-actions :default [state action-space]
  ((:fn action-space) state))
 
;(defn applicable-actions [state action-space]
;  ((:fn action-space) state))
  
(defn successor-states [state action-space]
  (map #(next-state state %) (applicable-actions state action-space)))
  




