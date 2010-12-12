
(defmacro init-repl []
  `(do (use 'edu.berkeley.ai.util)
       (require '[mycroft.main :as mycroft])
       (require '[angelic.search.implicit.subproblem-eval :as se])
       (require '[angelic.search.summaries :as summaries])
       (require '[angelic.search.summary :as summary])       
     ))

;
;
;(mycroft/run 8081)
