(ns angelic.search.explicit.depth-first
  (:require
   [angelic.env :as env]
   [angelic.hierarchy :as hierarchy]
   [angelic.hierarchy.util :as hierarchy-util]      
   [angelic.search.explicit.hierarchical :as eh])
  (:import java.util.HashMap)
  )

;; Returns hfs solution better than bound or nil.
(defn dfbb* [root children bound]
  (when (>= (:reward root) bound)
    (if (empty? (:remaining-actions root))
      (eh/hfs-solution-pair root)
      (loop [c (children root) best nil bound bound]
        (if-let [[f & r] (seq c)]
          (if-let [rec (dfbb* f children bound)]
            (recur r rec (second rec))
            (recur r best bound))
          best)))))

(defn make-root-hfs [henv]
  (let [e (hierarchy/env henv)]
   (eh/make-root-hfs
    (env/initial-state e)
    (hierarchy-util/make-top-level-action e [(hierarchy/initial-plan henv)]))))

(defn dfbb [henv & [init-bound]]
  (dfbb*
   (make-root-hfs henv)
   #_ eh/hfs-children  (comp shuffle eh/hfs-children)
   (or init-bound Double/NEGATIVE_INFINITY)))

(defn graph-dfbb* [root children ^HashMap m bound]
  (when (>= (:reward root) bound)
    (let [k ((juxt :state :remaining-actions) root)]
      (when (>= (:reward root) (get m k Double/NEGATIVE_INFINITY))
        (.put m k (:reward root))
        (if (empty? (:remaining-actions root))
          (eh/hfs-solution-pair root)
          (loop [c (children root) best nil bound bound]
            (if-let [[f & r] (seq c)]
              (if-let [rec (graph-dfbb* f children m bound)]
                (recur r rec (second rec))
                (recur r best bound))
              best)))))))

(defn graph-dfbb [henv & [init-bound]]
  (graph-dfbb*
   (make-root-hfs henv)
   #_ eh/hfs-children (comp shuffle eh/hfs-children)
   (HashMap.)
   (or init-bound Double/NEGATIVE_INFINITY)))
