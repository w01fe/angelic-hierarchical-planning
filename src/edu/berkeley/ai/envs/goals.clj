(ns edu.berkeley.angel.envs)

(defstruct goal :class :test)

(defn make-goal [test]
  (struct goal ::Goal test))

(defn satisfies-goal? [state goal]
  ((:test goal) state))




