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
; :const {[size] [freespace] [legal-go] [goal o] [base-offsets] [n-base-samples] [map]...}
;    freespace is set of free [x y] pairs (for base).
;    legal-go is set of allowed [gxo gyo] pairs
;    goal is now set of allowed positions. Previously: [[minx miny] [maxx maxy]] range -- inclusive.
;    base-offsets is randomized list of offset positions to drasp/drop at a position.
; [base],  current "base" coordinates.
; [gripper-offset], gripper coordinate offsets
; [pos o], location of object
; [at-goal? o] - true/false 
; [object-at [x y]] - nil, object, or :border
; [holding] - object or nil
; [parked?]

; implicit obstacle border.

; can grasp from any direction (gripper next to obj).
; For "fairness", only allow putdown in goal region ? 

;; Note: dynamics require that evenn if object is initially in goal region, 
; you must pick it up and put it down again. 

; Actions:
; unpark, u/d/l/r, park (for base)
; gu/gl/gr/gl
; pickup-l/r/d/u
; drop-l/r/d/u

(def dirs [[:l [-1 0]] [:r [1 0]] [:u [0 -1]] [:d [0 1]]])

(defn add-pos
  ([[x1 y1] [x2 y2]] [(+ x1 x2) (+ y1 y2)])
  ([[x1 y1] [x2 y2] [x3 y3]] [(+ x1 x2 x3) (+ y1 y2 y3)]))

(defn sub-pos
  ([[x1 y1] [x2 y2]] [(- x1 x2) (- y1 y2)]))

(defn region-contains? [[[minx miny] [maxx maxy]] [x y]]
  (and (<= minx x maxx) (<= miny y maxy)))

(defn region-cells [[[minx miny] [maxx maxy]]]
  (for [x (range minx (inc maxx)), y (range miny (inc maxy))] [x y]))

(defn make-random [seed]
  (doto (Random. (long seed)) (.nextDouble) (.nextDouble)))

(defn pseudo-shuffle [#^Random r #^java.util.Collection coll]
  (seq (doto (java.util.ArrayList. coll) (java.util.Collections/shuffle r))))

(defn spiral-to [max-d] 
  (cons [0 0] 
    (apply concat 
      (for [d (range 1 (inc max-d)), i (range d)]
        [[i (- d i)]     [(- i) (- i d)] 
         [(- d i) (- i)] [(- i d) i]]))))

; Note, unlike previous domains, here still require precondition verification.

(defn make-park [s]
  (env/FactoredPrimitive [:park] {[:parked?] false} {[:parked?] true} -5))

(defn make-unpark [s]
  (env/FactoredPrimitive [:unpark] {[:parked?] true [:gripper-offset] [0 0]} {[:parked?] false} -5))

(defn make-base-dir [s [dirname dir]]
  (let [const (env/get-var s :const)
        base  (env/get-var s [:base])
        nbase (add-pos base dir)]
    (when (contains? (get const [:freespace]) nbase)
      (env/FactoredPrimitive 
       [:base dirname]
       {[:base] base [:parked?] false}
       {[:base] nbase}
       -2))))

(defn make-gripper-dir [s [dirname dir]]
  (let [const (env/get-var s :const)
        base  (env/get-var s [:base])
        go    (env/get-var s [:gripper-offset])
        ngo   (add-pos go dir)
        npos  (add-pos ngo base)]
    (when (contains? (get const [:legal-go]) ngo)
      (env/FactoredPrimitive 
       [:gripper dirname]
       {[:base] base [:gripper-offset] go [:parked?] true 
        [:object-at npos] nil}
       {[:gripper-offset] ngo}
       -1))))

(defn make-pickup [dirname base go o opos]
  (env/FactoredPrimitive 
   [:pickup dirname]
   {[:base] base [:gripper-offset] go [:parked?] true 
    [:pos o] opos [:holding] nil [:at-goal? o] false}
   {[:pos o] nil [:holding] o [:object-at opos] nil}
   -1))

(defn make-pickup-dir [s [dirname dir]]
  (let [base  (env/get-var s [:base])
        go    (env/get-var s [:gripper-offset])
        opos  (add-pos base go dir)
        o     (env/get-var s [:object-at opos])]
    (when (and o (not (= o :border)))
      (make-pickup dirname base go o opos))))

(defn make-putdown [dirname base go o opos]
  (env/FactoredPrimitive 
       [:putdown dirname]
       {[:base] base [:gripper-offset] go [:parked?] true 
        [:holding] o [:object-at opos] nil}
       {[:pos o] opos [:holding] nil [:object-at opos] o [:at-goal? o] true}
       -1))

(defn make-putdown-dir [s [dirname dir]]
  (let [const (env/get-var s :const)
        o     (env/get-var s [:holding])
        base  (env/get-var s [:base])
        go    (env/get-var s [:gripper-offset])
        opos  (add-pos base go dir)]
    (when (and o (contains? (get const [:goal o]) opos))
      (make-putdown dirname base go o opos))))


; obstacles are [[minx miny] [maxx maxy]]
; goals are sets os positions.
; objects are [name [cx cy] goal-pos-set] -- no goal means static 
; g-rad is gripper "radius" -- diamond shaped.

; Note, if you pass unreachable goal positions this will suffer.
(defn make-2d-manipulation-env 
  ([size base obstacles objects g-rad]
     (make-2d-manipulation-env size base obstacles objects g-rad Integer/MAX_VALUE))
  ([size base obstacles objects g-rad n-base-samples]
     (make-2d-manipulation-env size base obstacles objects g-rad n-base-samples (make-random 1)))  
  ([size base obstacles objects g-rad n-base-samples #^Random random]
  (let [[width height] size
        border-regions [[[0 0] [0 height]] [[width 0] [width height]]
                        [[0 0] [width 0]] [[0 height] [width height]]]
        border-cells   (set (mapcat region-cells border-regions))
        obstacle-cells (set (mapcat region-cells obstacles))
        all-cells      (set (region-cells [[0 0] size]))
        freespace      (clojure.set/difference all-cells border-cells obstacle-cells)
        legal-go       (set (spiral-to g-rad))]
    (env/SimpleFactoredEnv
     (into {:const (into {[:size] size [:freespace] freespace [:legal-go] legal-go [:objects] objects
                          [:base-offsets] (pseudo-shuffle random (spiral-to (inc g-rad)) )
                          [:n-base-samples] n-base-samples
                          [:map] (reduce (fn [m [x y]] (assoc-in m [y x] \.))
                                   (reduce (fn [m [x y]] (assoc-in m [y x] \*))
                                      (vec (repeat (inc height) (vec (repeat (inc width) \ ))))
                                      border-cells)
                                   obstacle-cells)}
                         (for [[o _ goal] objects :when goal] [[:goal o] (set goal)]))
            [:base] base [:gripper-offset] [0 0] [:holding] nil [:parked?] true}
           (apply concat
            (for [cell all-cells]    [[:object-at cell] nil])
            (for [cell border-cells] [[:object-at cell] :border])
            (for [[o opos goal] objects]
              [[[:pos o] opos] 
               [[:at-goal? o] (if goal false true)] 
               [[:object-at opos] o]])))
     (fn [s]
       (filter #(and % (env/applicable? % s))
          (apply concat
            [(make-park s) (make-unpark s)]
            (for [dir dirs]
              [(make-base-dir s dir) (make-gripper-dir s dir)
               (make-pickup-dir s dir) (make-putdown-dir s dir)]))))
     (into {[:parked?] true [:gripper-offset] [0 0]} 
           (for [[o _ goal] objects :when goal] [[:at-goal? o] true]))))))

; (print-state (initial-state (make-2d-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] #{ [4 4] } ] ] 2)))
; (uniform-cost-search (make-2d-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] #{ [4 4] } ] ] 2))


;; Same as above, but objects can have goal regions, we'll sample reachable positions.
;; TODO: copy pasta is rather verbose, etc.  
(defn make-2d-manipulation-env-regions 
  ([size base obstacles objects g-rad n-base-samples n-goal-samples]
     (make-2d-manipulation-env-regions size base obstacles objects g-rad
                                       n-base-samples n-goal-samples 1))  
  ([size base obstacles objects g-rad n-base-samples n-goal-samples seed]
     (let [[width height] size
           border-regions [[[0 0] [0 height]] [[width 0] [width height]]
                           [[0 0] [width 0]] [[0 height] [width height]]]
           border-cells   (set (mapcat region-cells border-regions))
           obstacle-cells (set (mapcat region-cells obstacles))
           all-cells      (set (region-cells [[0 0] size]))
           freespace      (clojure.set/difference all-cells border-cells obstacle-cells)
           reach-spiral   (spiral-to (inc g-rad))
           random         (Random. (long seed))]
       (make-2d-manipulation-env
        size base obstacles
        (for [[oname opos goal] objects]
          [oname opos
           (->> goal
                region-cells
                (pseudo-shuffle random )
                (filter (fn [c] (some #(freespace (add-pos c %)) reach-spiral)))
                (take n-goal-samples)
                set)])
        g-rad n-base-samples random))))

; (uniform-cost-search (make-2d-manipulation-env-regions [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] [ [4 4] [4 4 ] ] ] ] 2 2 2))



(defn state-map [s]
  (let [const   (env/get-var s :const)
        base    (env/get-var s [:base])
        go      (env/get-var s [:gripper-offset])]
    (reduce (partial apply assoc-in)
            (get const [:map])
            (concat 
             [[(add-pos base go) \G]
              [base              \B]]
             (for [[o] (get const [:objects])]
               [(env/get-var s [:pos o]) (first (name o))])))))

(defn state-str [s]
  (apply str (util/str-join "\n" (map (partial apply str) (state-map s))) "\n"
         (concat (if (env/get-var s [:parked?]) "parked" "unparked") 
                 (if-let [h (env/get-var s [:holding])] [", holding " h "\n"] ["\n"]))))

(defn print-state [s] (print (state-str s)))



(defn reach-context 
  ([s] (reach-context s (env/get-var s [:base])))
  ([s base]
    (into #{[:base] [:gripper-offset]}
      (for [go (util/safe-get (env/get-var s :const) [:legal-go])]
        [:object-at (add-pos base go)]))))

(defn make-reach-hla [env dst-go] 
  (reify  :as this
    env/Action                (action-name [] [:reach dst-go])
                              (primitive? [] false)
    env/ContextualAction      (precondition-context [s] (reach-context s))
    hierarchy/HighLevelAction (immediate-refinements- [s]
                                (if (= dst-go (env/get-var s [:gripper-pos]))
                                    [[]]
                                  (for [dir dirs] [(make-gripper-dir s dir) this])))
                              (cycle-level- [s] 1)))
; manhattan, SLD?  range?

(defn make-grasp-hla [env o] 
 (reify :as this
  env/Action                (action-name [] [:grasp o])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (conj (reach-context s) [:pos o] [:at-goal? o] [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [base (env/get-var s [:base])
                                   opos (env/get-var s [:pos o])]
                               (for [[dirname dir] dirs]
                                 (let [gpos (sub-pos opos dir)
                                       go   (sub-pos gpos base)]
                                   [(make-reach-hla env go)
                                    (make-pickup dirname base go o opos)]))))
                            (cycle-level- [s] nil)))
;manhattan
;pess: SLD?  

(defn make-drop-at-hla [env o dst]
 (reify :as this
  env/Action                (action-name [] [:drop-at o dst])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (conj (reach-context s) [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [base (env/get-var s [:base])]
                               (for [[dirname dir] dirs]
                                 (let [gpos (sub-pos dst dir)
                                       go   (sub-pos gpos base)]
                                   [(make-reach-hla env go)
                                    (make-putdown dirname base go o dst)]))))
                            (cycle-level- [s] nil)))
;manhattan
;pess: SLD?  




;; TODO: should nav be done by external alg, (fairest between angelic/not) or explicit? 
(defn make-nav-hla [env dst] 
 (reify :as this
  env/Action                (action-name [] [:nav dst])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] #{[:base]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (if (= dst (env/get-var s [:base]))
                               [[]]
                               (for [dir dirs] [(make-base-dir s dir) this])))
                            (cycle-level- [s] 1)))
; manhattan
; pess? SLD? (try direct line, if occ then -inf).

(defn make-move-base-hla [env dst]
 (reify  :as this
  env/Action                (action-name [] [:move-base dst])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] #{[:base] [:parked?] [:gripper-offset]})
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [base (env/get-var s [:base])]
                               (if (= base dst)
                                  [[]]
                                 [[(ReachHLA env [0 0]) (make-unpark s) 
                                   (NavHLA dst) (make-park s)]])))
                            (cycle-level- [s] nil)))
; manhattan + park (if appl)
; pess? SLD?

;; TODO: check out state abstraction here

(defn make-go-grasp-hla [env o] 
 (reify :as this
  env/Action                (action-name [] [:go-grasp o])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (conj (reach-context s (env/get-var s [:pos o])) 
                                    [:pos o] [:at-goal? o] [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [const (env/get-var s :const)
                                   free  (get const [:freespace])
                                   opos  (env/get-var s [:pos o])]
                               (for [dst (->> (get const [:base-offsets])
                                              (map #(add-pos % opos))
                                              (filter free)
                                              (take (get const [:n-base-samples])))]
                                 [(make-move-base-hla env dst) (make-grasp-hla env o)])))
                            (cycle-level- [s] nil)))

(defn make-go-drop-at-hla [env o o-dst] 
 (reify :as this
  env/Action                (action-name [] [:go-drop-at o o-dst])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s]
                              (conj (reach-context s o-dst) [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (let [const (env/get-var s :const)
                                   free  (get const [:freespace])]
                               (for [dst (->> (get const [:base-offsets])
                                              (map #(add-pos % o-dst))
                                              (filter free)
                                              (take (get const [:n-base-samples])))]
                                 [(make-move-base-hla env dst) (make-drop-at-hla env o o-dst)])))
                            (cycle-level- [s] nil)))

(defn make-go-drop-hla [env o] 
 (reify :as this
  env/Action                (action-name [] [:go-drop o])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (conj (apply clojure.set/union 
                                     (map #(reach-context s %) 
                                          (get (env/get-var s :const) [:goal o]))) 
                                    [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                             (for [o-dst (get (env/get-var s :const) [:goal o])]
                               [(make-go-drop-at-hla env o o-dst)]))
                            (cycle-level- [s] nil)))

(defn make-move-to-goal-hla [env o] 
 (reify :as this
  env/Action                (action-name [] [:go-drop o])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] 
                              (conj (apply clojure.set/union 
                                     (map #(reach-context s %) 
                                          (cons (env/get-var s [:pos o])
                                                (get (env/get-var s :const) [:goal o])))) 
                                    [:holding]))
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              [[(make-go-grasp-hla env o) (make-go-drop-hla env o)]])
                            (cycle-level- [s] nil)))

;; TODO: can do better on context -- probably rarely matters?
(defn- make-tla [env]
 (let [context (util/keyset (dissoc (env/initial-state env) :const))]
 (reify :as this
  env/Action                (action-name [] [:act])
                            (primitive? [] false)
  env/ContextualAction      (precondition-context [s] context)
  hierarchy/HighLevelAction (immediate-refinements- [s]
                              (let [remaining (remove #(env/get-var s [:at-goal? %])
                                               (map first (get (env/get-var s :const) [:objects])))]
                                (if (empty? remaining)
                                    [[]]
                                  (for [o remaining] [(make-move-to-goal-hla env o) this]))))
                            (cycle-level- [s] 2))))

(defn make-2d-manipulation-hierarchy [env]
  (hierarchy/SimpleHierarchicalEnv env [(make-tla env)]))



; MoveToGoal
; Act

;; Do we sample base, drop positions, or enumerate ? 




; (print-state (initial-state (make-2d-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] [ [4 4] [4 4] ] ] ] 2))) 