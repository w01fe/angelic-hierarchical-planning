(ns edu.berkeley.ai.load-all)

(doseq [sub-ns '[util envs search angelic domains scripts]]
  (require (symbol (str "edu.berkeley.ai." sub-ns ".load-all"))))

