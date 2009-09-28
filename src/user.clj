(defn l [] (require 'edu.berkeley.ai.load-all :reload-all))

(defn symbol-append [s1 s2]
  (symbol (apply str (concat (name s1) (name s2)))))

(defmacro u [& args] 
  `(do (l) (use ~@(map #(list 'quote (if (coll? %) (cons (symbol-append 'edu.berkeley.ai. (first %)) (rest %)) (symbol-append 'edu.berkeley.ai. %))) args))))

  
(defn uall [] 
  (u util 
       util.charts util.datasets util.disjoint-sets util.graphs
       util.graphviz util.hybrid util.pdf util.propositions util.queues util.lp    
     envs envs.states.binary envs.states.explicit
       envs.strips envs.strips.smart-csps 
       envs.hybrid-strips envs.hybrid-strips.hybrid-constraints
       envs.hybrid-strips.hybrid-effects ;envs.hybrid-strips.hybrid-lp-states
     search
       search.state-space
       search.algorithms.real-time search.algorithms.textbook
     angelic 
       angelic.dnf-valuations angelic.ncstrips-descriptions
       angelic.hierarchies
         angelic.hierarchies.flat-hierarchies angelic.hierarchies.strips-hierarchies
	 angelic.hierarchies.abstract-lookahead-graphs angelic.hierarchies.abstract-lookahead-trees
	 angelic.hierarchies.offline-algorithms angelic.hierarchies.online-algorithms
     ;domains
       domains.nav-switch domains.warehouse domains.vac-rooms domains.discrete-road-trip
       domains.hybrid-blocks domains.road-trip domains.simple-road-trip
     scripts.experiments scripts.z09-icaps08-tr ;scripts.z09-aij scripts.z09-aima
     ))












;   util envs search search.algorithms.textbook angelic angelic.hierarchies domains.nav-switch domains.strips  angelic.dnf-valuations angelic.ncstrips-descriptions angelic.hierarchies.strips-hierarchies util.queues util.graphs domains.warehouse  domains.discrete-road-trip domains.road-trip angelic.hierarchies.abstract-lookahead-trees angelic.hierarchies.abstract-lookahead-graphs #_ angelic.hierarchies.clause-graphs angelic.hierarchies.offline-algorithms angelic.hierarchies.online-algorithms scripts.experiments scripts.cluster #_ scripts.z09-aij scripts.z09-icaps08-tr scripts.z09-aima util.datasets util.charts util.graphviz scripts.timing-warehouse scripts.timing-nav-switch ))
; domains.hybrid-strips domains.hybrid-blocks

(defmacro uros []
  `(do
     (uall)
     (use 'ros.ros 'ros.world 'ros.geometry 'ros.robot 'ros.robot-actions 'ros.robot-hierarchy) 
     (~'import-ros) 
     (~'import-all-msgs-and-srvs)
     #_(def nh (~'make-node-handle))))

(comment 
(defn lr [] (require '[ros ros nav] :reload-all))

(defmacro ur [& args] 
  `(do (lr) 
       (import ~'[ros Ros NodeHandle RosException Publisher Subscriber Subscriber$Callback Subscriber$QueueingCallback ServiceClient ServiceServer ServiceServer$Callback]
	       )
       (use ~@(map #(list 'quote (if (coll? %) (cons (symbol-append 'ros. (first %)) (rest %)) (symbol-append 'ros. %))) args))))

(defn uros [] (ur ros nav)))

; These may be useful but cause gui to load
(use 'clojure.inspector 'clojure.test)  


;(use 'clj-backtrace.repl '(clojure.contrib cond condt duck-streams fcase javadoc lazy-seqs repl-utils seq-utils str-utils template trace walk))


     
;(set! *warn-on-reflection* true)      
      
;(u util)  