(ns angelic.search.incremental.lattices
  (:require [edu.berkeley.ai.util :as util]
            #_  [angelic.search.incremental.summary :as summary])
  (:import [java.util HashMap List ArrayList]))

;; This file defines a declarative framework for maintaining consistency
;; between a set of subsumption lattices.

;; Lattices can only grow downward.  When a lattice grows, it notifies
;; all watchers about the extension.

;; Various kinds of lattices exist that do different things out-of-the-box.

;; WrappedLattice -- maintains node-by-node connection
;; ActionInRefinement input is simple delta-wrapper of previous input
;; OutputLattice of action watches OutputLattices of final AIRs ?
;; OutputLattice of AIR is contextifying wrapper of sub-output.
;; Only remaining question is how to collect final outputs.
;; Options: actually connect them,
;; Or just provide a mechanism to add watchers to all.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Lattice ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Protocol ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Need two types of links - parent and sup
;; Either need multi-parents for DAG, or keep main thing as tree.

(defprotocol IOLattice)


(comment ; Old tree verisons.
  (defprotocol Lattice)

  (defprotocol PLatticeNode
    (lattice      [ln])
    (parent       [ln])
    (node-key     [ln] "i.e. ,state set")
    (node-data    [ln] "arbitrary")  
    (child-map    [ln] "HashMap")
    (add-watcher! [ln watcher] "A watcher is just a 2-arg fn of parent-node child-node")
    (add-child!   [ln node-key node-data]))

  (declare make-lattice-node)

  (defrecord LatticeNode [lattice parent node-key node-data ^HashMap child-map ^List watchers]
    PLatticeNode
    (lattice      [ln]   lattice)
    (parent       [ln]   parent)
    (node-key     [ln]   node-key)
    (node-data    [ln]   node-data)  
    (child-map    [ln]   child-map)
    (add-watcher! [ln watcher]
                  (.add watchers watcher)
                  (doseq [[data child] child-map]
                    (watcher ln child)))
    (add-child!   [ln child-key child-data]
                  (when-not (.containsKey child-map child-key)
                    (let [child (make-lattice-node lattice ln child-key child-data)]
                      (.put child-map chid-key child)
                      (doseq [watcher (seq watchers)] (watcher ln child))
                      child))))

  (defn make-lattice-node [lattice parent node-key node-data]
    (LatticeNode. lattice parent node-key node-data (HashMap.) (ArrayList.)))

  (defn- add-child-transform-watch! [root transformed-root key-fn data-fn]
    (add-watcher! root
                  (fn [watched new-child-node]
                    (add-child-transform-watch!
                     new-child-node
                     (add-child! transformed-root (key-fn new-child-node) (data-fn new-child-node))
                     key-fn data-fn))))

  (defn make-transformed-lattice [other-root key-fn data-fn]
    (let [new-root (make-lattice-node nil nil (key-fn other-root) (data-fn other-root))]
      (add-child-transform-watch! other-root new-root key-fn data-fn)
      new-root))

  (defn make-lattice-watcher [node-watcher]
    (fn [watched new-child-node]
      (node-watcher watched new-child-node)
      (add-watcher! new-child-node node-watcher)))

  (defn start-copy [source-root target-root]
    (add-watcher! source-root
                  #(start-copy %2 (add-child! target-root (node-key %2) (node-data %2)))))


  (defn make-union-lattice [#_ ???])





  (comment
    ;; TODO: get rid of factory? 
    (defprotocol LatticeNodeFactory
      (create-child [lnf parent child-data]))
    (defn make-simple-lattice-node-factory []
      (reify LatticeNodeFactory
             (create-child [lnf parent child-data]
                           (LatticeNode. nil parent child-data (HashMap.) (ArrayList.) lnf)))))




)