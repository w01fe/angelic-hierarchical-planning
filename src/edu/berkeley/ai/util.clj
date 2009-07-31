(ns edu.berkeley.ai.util
 (:use clojure.test))

(doseq [file '[contrib macros seqs sets maps probability files misc numeric polytopes timing]]
   (load-file (str "util/" file ".clj")))


