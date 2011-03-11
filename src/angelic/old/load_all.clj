(ns angelic.old.load-all)

(require 'angelic.util)
(doseq [sub-ns '[envs search angelic domains scripts]]
  (require (symbol (str "angelic.old." sub-ns ".load-all"))))

