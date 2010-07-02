(ns exp.2d-manipulation
;  (:use clojure.test)
  (:require [edu.berkeley.ai.util :as util]
            [exp [env :as env] [sas :as sas] [hierarchy :as hierarchy]])
  (:import [java.util Random]))

; This is meant to be a simplified version of the ICAPS '10/SAHTN 
; mobile manipulation domain.  In particular, we abstract away most of
; the robot, while trying to maintain the same domain structures.

; This could be done as discrete or continuous.  Doesn't really matter here,
; but we need to decide how we're handling angelic sets, etc. 
; May as well be discrete, so we can use SAS machinery.

; Seems we need all the angelic machinery we had before, in general case.

;; State variables are (all keyworded, note!):
; :const {[size] [freespace] [legal-go] [goal o] [map]...}
;    freespace is set of free [x y] pairs (for base).
;    legal-go is set of allowed [gxo gyo] pairs
;    goal is [[minx miny] [maxx maxy]] range -- inclusive.
; [bx], [by] - current "base" coordinates.
; [gxo], [gyo] - gripper x and y offsets.  
; [x o], [y o] - location of object
; [at-goal? o] - 
; [object-at x y] - nil, object, or :border
; [holding]
; [parked?]

; implicit obstacle border.

; can grasp from any direction (gripper next to obj).
; For "fairness", only allow putdown in goal region ? 

; Actions:
; unpark, u/d/l/r, park (for base)
; gu/gl/gr/gl
; pickup-l/r/d/u
; drop-l/r/d/u

(def dirs [[:l -1 0] [:r 1 0] [:u 0 -1] [:d 0 1]])

; Note, unlike previous domains, here still require precondition verification.

(defn make-park [s]
  (env/FactoredPrimitive [:park] {[:parked?] false} {[:parked?] true} -5))

(defn make-unpark [s]
  (env/FactoredPrimitive [:unpark] {[:parked?] true [:gxo] 0 [:gyo] 0} {[:parked?] false} -5))

(defn make-base-dir [s [dirname dx dy]]
  (let [const (env/get-var s :const)
        cx    (env/get-var s [:bx])
        cy    (env/get-var s [:by])
        nx    (+ cx dx)
        ny    (+ cy dy)]
    (when (contains? (get const [:freespace]) [nx ny])
      (env/FactoredPrimitive 
       [:base dirname]
       {[:bx] cx [:by] cy [:parked?] false}
       {[:bx] nx [:by] ny}
       -2))))

(defn make-gripper-dir [s [dirname dx dy]]
  (let [const (env/get-var s :const)
        cbx   (env/get-var s [:bx])
        cby   (env/get-var s [:by])
        cgxo  (env/get-var s [:gxo])
        cgyo  (env/get-var s [:gyo])        
        ngxo  (+ cgxo dx)
        ngyo  (+ cgyo dy)]
    (when (contains? (get const [:legal-go]) [ngxo ngyo])
      (env/FactoredPrimitive 
       [:gripper dirname]
       {[:bx] cbx [:by] cby [:gxo] cgxo [:gyo] cgyo [:parked?] true 
        [:object-at (+ cbx ngxo) (+ cby ngyo)] nil}
       {[:gxo] ngxo [:gyo] ngyo}
       -1))))

(defn make-pickup-dir [s [dirname dx dy]]
  (let [cbx   (env/get-var s [:bx])
        cby   (env/get-var s [:by])
        cgxo  (env/get-var s [:gxo])
        cgyo  (env/get-var s [:gyo])        
        ox    (+ cbx cgxo dx)
        oy    (+ cby cgyo dy)
        o     (env/get-var s [:object-at ox oy])]
    (when (and o (not (= o :border)))
      (env/FactoredPrimitive 
       [:pickup dirname]
       {[:bx] cbx [:by] cby [:gxo] cgxo [:gyo] cgyo [:parked?] true 
        [:x o] ox [:y o] oy [:holding] nil [:at-goal? o] false}
       {[:x o] nil [:y o] nil [:holding] o [:object-at ox oy] nil}
       -1))))

(defn region-contains? [[[minx miny] [maxx maxy]] [x y]]
  (and (<= minx x maxx) (<= miny y maxy)))

(defn make-putdown-dir [s [dirname dx dy]]
  (let [const (env/get-var s :const)
        o     (env/get-var s [:holding])
        cbx   (env/get-var s [:bx])
        cby   (env/get-var s [:by])
        cgxo  (env/get-var s [:gxo])
        cgyo  (env/get-var s [:gyo])        
        ox    (+ cbx cgxo dx)
        oy    (+ cby cgyo dy)]
    (when (and o (region-contains? (get const [:goal o]) [ox oy]))
      (env/FactoredPrimitive 
       [:putdown dirname]
       {[:bx] cbx [:by] cby [:gxo] cgxo [:gyo] cgyo [:parked?] true 
        [:holding] o [:object-at ox oy] nil}
       {[:x o] ox [:y o] oy [:holding] nil [:object-at ox oy] o [:at-goal? o] true}
       -1))))


; obstacles and goals are [[minx miny] [maxx maxy]]
; objects are [name [cx cy] goal] -- no goal means static 
; g-rad is gripper "radius" -- diamond shaped.

(defn region-cells [[[minx miny] [maxx maxy]]]
  (for [x (range minx (inc maxx)), y (range miny (inc maxy))] [x y]))

(defn make-2d-manipulation-env [size start obstacles objects g-rad]
  (let [[width height] size
        [bx by]        start
        border-regions [[[0 0] [0 height]] [[width 0] [width height]]
                        [[0 0] [width 0]] [[0 height] [width height]]]
        border-cells   (set (mapcat region-cells border-regions))
        obstacle-cells (set (mapcat region-cells obstacles))
        all-cells      (set (region-cells [[0 0] size]))
        freespace      (clojure.set/difference all-cells border-cells obstacle-cells)
        legal-go       (set (filter (fn [[x y]] (<= (+ (util/abs x) (util/abs y)) g-rad))
                                    (region-cells [[(- g-rad) (- g-rad)] [g-rad g-rad]])))]
    (env/SimpleFactoredEnv
     (into {:const (into {[:size] size [:freespace] freespace [:legal-go] legal-go [:objects] objects
                          [:map] (reduce (fn [m [x y]] (assoc-in m [y x] \.))
                                   (reduce (fn [m [x y]] (assoc-in m [y x] \*))
                                      (vec (repeat (inc height) (vec (repeat (inc width) \ ))))
                                      border-cells)
                                   obstacle-cells)}
                         (for [[o _ goal] objects :when goal] [[:goal o] goal]))
            [:bx] bx [:by] by [:gxo] 0 [:gyo] 0 [:holding] nil [:parked?] true}
           (apply concat
            (for [[x y] all-cells]     [[:object-at x y] nil])
            (for [[x y] border-cells] [[:object-at x y] :border])
            (for [[o [ox oy] goal] objects]
              [[[:x o] ox] [[:y o] oy] 
               [[:at-goal? o] (if goal false true)] 
               [[:object-at ox oy] o]])))
     (fn [s]
       (filter #(and % (env/applicable? % s))
          (apply concat
            [(make-park s) (make-unpark s)]
            (for [dir dirs]
              [(make-base-dir s dir) (make-gripper-dir s dir)
               (make-pickup-dir s dir) (make-putdown-dir s dir)]))))
     (into {[:parked?] true [:gxo] 0 [:gyo] 0} 
           (for [[o _ goal] objects :when goal] [[:at-goal? o] true])))))

(defn state-map [s]
  (let [const   (env/get-var s :const)
        bx      (env/get-var s [:bx])
        by      (env/get-var s [:by])
        gxo     (env/get-var s [:gxo])
        gyo     (env/get-var s [:gyo])]
    (reduce (partial apply assoc-in)
            (get const [:map])
            (concat 
             [[[(+ bx gxo) (+ by gyo)] \G]
              [[bx by]                 \B]]
             (for [[o] (get const [:objects])]
               [[(env/get-var s [:x o]) (env/get-var s [:y o])] (first (name o))])))))

(defn state-str [s]
  (apply str (util/str-join "\n" (map (partial apply str) (state-map s))) "\n"
         (concat (if (env/get-var s [:parked?]) "parked" "unparked") 
                 (if-let [h (env/get-var s [:holding])] [", holding " h "\n"] ["\n"]))))

(defn print-state [s] (print (state-str s)))


; (print-state (initial-state (make-2d-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] [ [4 4] [4 4] ] ] ] 2))) 