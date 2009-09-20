(ns edu.berkeley.ai.util.disjoint-sets
  (:import java.util.HashMap)
  (:use edu.berkeley.ai.util)
  )

; Simple disjoint-set algorithms.
(set! *warn-on-reflection* true)

(defstruct disjoint-sets :class :node-map)

(defn ds-make-set [#^HashMap ds o]
  (let [a #^"[Ljava.lang.Object;" (to-array [o 0 nil])]
    (aset a 2 a)
    (.put ds o a)
    o))

(defn- ds-find- [#^"[Ljava.lang.Object;" a]
  (let [p         (aget a 2)]
    (if (identical? a p) 
        (do (aset a 1 0)
	    a)
      (let [np (ds-find- p)]
	(aset a 2 np)
	(aset a 1 1)
	np))))

(defn ds-find [#^HashMap ds o]
  (aget #^"[Ljava.lang.Object;" (ds-find- (.get ds o)) 0))

(defn ds-separate? [#^HashMap ds o1 o2]
  (not (identical? (ds-find ds o1) (ds-find ds o2))))

(defn ds-union [#^HashMap ds o1 o2]
  (let [#^"[Ljava.lang.Object;" a1 (ds-find- (.get ds o1))
	#^"[Ljava.lang.Object;" a2 (ds-find- (.get ds o2))
	r1         (aget a1 1)
	r2         (aget a2 1)]
    (cond (> r1 r2) 
	    (do (aset a2 2 a1)
		(aget a1 0))
	  (< r1 r2)
	    (do (aset a1 2 a2)
		(aget a2 0))
	  (identical? a1 a2)
	    (aget a1 0)
	  :else
	    (do (aset a2 2 a1)
		(aset a1 1 (inc (aget a1 1)))
		(aget a1 0)))))

(defn make-disjoint-sets
  ([] (make-disjoint-sets []))
  ([objs]
     (let [h (HashMap.)]
       (doseq [o objs] (ds-make-set h o))
       h)))


(set! *warn-on-reflection* false)

  

    

  
  

       
  
  

