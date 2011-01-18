
(defmacro init-repl []
  '(do (use 'edu.berkeley.ai.util)
      (require '[mycroft.main :as mycroft])
      (require '[angelic.search.summary-graphs :as sg])
      (require '[angelic.search.summary :as summary])       
     ))

;
;
;(mycroft/run 8081)
