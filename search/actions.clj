;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.states.clj
;;
;;  Exports for states. 

(ns angel.search)

(defstruct action :name :function)

(defn make-action [name function]
  (struct action name function))

(defn apply-action [state action]
  ((:function action) state))




