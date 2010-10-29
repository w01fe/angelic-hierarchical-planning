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

(defprotocol Lattice)

(defprotocol PLatticeNode
  (lattice      [ln])
  (parent       [ln])
  (data         [ln] "i.e. ,state set")
  (child-map    [ln] "HashMap")
  (add-watcher! [ln watcher])
  (add-child!   [ln data]))

(defprotocol LatticeNodeWatcher
  (notify-new-child! [watcher watched new-child-node]))

(declare make-lattice-node)

(defrecord LatticeNode [lattice parent data ^HashMap child-map ^List watchers]
  PLatticeNode
  (lattice      [ln]   lattice)
  (parent       [ln]   parent)
  (data         [ln]   data)
  (child-map    [ln]   child-map)
  (add-watcher! [ln watcher]
    (.add watchers watcher)
    (doseq [[data child] child-map]
      (notify-new-child! watcher ln child)))
  (add-child!   [ln child-data]
    (when-not (.containsKey child-map child-data)
      (let [child (make-lattice-node lattice ln child-data)]
        (.put child-map data child)
        (doseq [watcher (seq watchers)] (notify-new-child! watcher ln child))
        child))))

(defn make-lattice-node [lattice parent data]
  (LatticeNode. lattice parent data  (HashMap.) (ArrayList.)))

(defn- add-child-transform-watch! [root transformed-root data-transform]
  (add-watcher! root
    (reify LatticeNodeWatcher
      (notify-new-child! [watcher watched new-child-node]
        (add-child-transform-watch!
         new-child-node
         (add-child! transformed-root (data-transform (data new-child-node)))
         data-transform)))))

(defn make-transformed-lattice [other-root data-transform]
  (let [new-root (make-lattice-node nil nil (data-transform (data other-root)))]
    (add-child-transform-watch! other-root new-root data-transform)
    new-root))


(defn make-union-lattice [#_ ???])





(comment
  ;; TODO: get rid of factory? 
(defprotocol LatticeNodeFactory
  (create-child [lnf parent child-data]))
(defn make-simple-lattice-node-factory []
  (reify LatticeNodeFactory
    (create-child [lnf parent child-data]
      (LatticeNode. nil parent child-data (HashMap.) (ArrayList.) lnf)))))




