(defn l [] (require 'edu.berkeley.ai :reload-all))

(defn symbol-append [s1 s2]
  (symbol (apply str (concat (name s1) (name s2)))))

(defmacro u [& args] 
  `(do (l) (use ~@(map #(list 'quote (if (coll? %) (cons (symbol-append 'edu.berkeley.ai. (first %)) (rest %)) (symbol-append 'edu.berkeley.ai. %))) args))))

  
(defn uall [] (u util envs search search.algorithms.textbook angelic angelic.hierarchies domains.nav-switch domains.strips  angelic.dnf-valuations angelic.ncstrips-descriptions angelic.hierarchies.strips-hierarchies util.queues util.graphs domains.warehouse  domains.discrete-road-trip domains.road-trip angelic.hierarchies.abstract-lookahead-trees angelic.hierarchies.abstract-lookahead-graphs angelic.hierarchies.offline-algorithms angelic.hierarchies.online-algorithms scripts.experiments scripts.cluster scripts.z09-aij util.datasets util.charts util.graphviz ))
; domains.hybrid-strips domains.hybrid-blocks

; These may be useful but cause gui to load
(use 'clojure.inspector)  


;(use 'clj-backtrace.repl '(clojure.contrib cond condt duck-streams fcase javadoc lazy-seqs repl-utils seq-utils str-utils template trace walk))



; No lazy love yet
;(require '[com.markmfredrickson.dejcartes :as chart])
  
;(import '(org.jfree.chart ChartFrame)) 
;(defn make-window [title chart]
;  (doto (ChartFrame. title chart)
;    (.pack)
;    (.setVisible true)))
      
;(set! *warn-on-reflection* true)      
      
;(u util)  