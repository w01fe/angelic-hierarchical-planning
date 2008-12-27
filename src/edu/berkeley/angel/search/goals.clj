;;  Copyright (c) Jason Wolfe, 2008. All rights reserved.    
;;  jawolfe at cs dot berkeley dot edu
;;
;;  File: angel.search.states.clj
;;
;;  Exports for states. 

(ns edu.berkeley.angel.search)

(defstruct goal :class :test)

(defn make-goal [test]
  (struct goal ::Goal test))

(defn satisfies-goal? [state goal]
  ((:test goal) state))




