(ns angelic.old.load-all)

(doseq [sub-ns '[util envs search angelic domains scripts]]
  (require (symbol (str "angelic.old." sub-ns ".load-all"))))

