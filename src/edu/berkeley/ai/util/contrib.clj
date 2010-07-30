(in-ns 'edu.berkeley.ai.util)

(require '[clojure.contrib.ns-utils :as ns-utils])

(require '[clojure.contrib.def :as def])

(defn slurp-ns [ns]
  (require ns)
  (doseq [v (ns-utils/ns-vars (ns-utils/get-ns ns))
	      :when (not (:deprecated (meta (resolve (symbol (str ns) (name v))))))
	      :when (not (#{"spit"} (name v)))]
    (eval `(def/defalias ~v ~(symbol (str ns "/" v))))))

(def *ns-to-slurp* '(cond combinatorics cond def duck-streams lazy-seqs math repl-utils seq shell-out str-utils trace))

(doseq [n *ns-to-slurp*]
  (slurp-ns (symbol (str 'clojure.contrib. n))))

