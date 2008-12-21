;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.states.clj
;;
;;  Exports for states. 

(ns edu.berkeley.angel.search)

; should use methods, not action fns ??????
; i.e. should be able to have same actions, use with different state representations?
; well, with the cost of a single function call can get that here ...? 

(defstruct action :class :name :fn)

(defn make-action [name function]
  (struct action ::Action name function))

(defn apply-action [state action]
  ((:fn action) state))




