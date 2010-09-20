(ns angelic.domains.discrete-manipulation
  (:require [edu.berkeley.ai.util :as util]
            [angelic.env :as env]
            [angelic.env.state :as state]            
            [angelic.env.util :as env-util]
            [angelic.hierarchy :as hierarchy]
            [angelic.hierarchy.angelic :as angelic]
            [angelic.hierarchy.state-set :as state-set]
            [angelic.hierarchy.util :as hierarchy-util])
  (:import [java.util Random]))

; This is meant to be a simplified version of the ICAPS '10/SAHTN 
; mobile manipulation domain.  In particular, we abstract away most of
; the robot, while trying to maintain the same domain structures.

; This could be done as discrete or continuous.  Doesn't really matter here,
; but we need to decide how we're handling angelic sets, etc. 
; May as well be discrete, so we can use SAS machinery.

; Seems we need all the angelic machinery we had before, in general case.

;; State variables are (all keyworded, note!):
; :const {[size] [freespace] [legal-go] [max-go] [goal o] [base-offsets] [n-base-samples] [map]...}
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

(def park-reward -5)
(def unpark-reward -2)

(defn make-park [s]
  (env-util/make-factored-primitive [:park] {[:parked?] false} {[:parked?] true} park-reward))

(defn make-unpark [s]
  (env-util/make-factored-primitive [:unpark] {[:parked?] true [:gripper-offset] [0 0]} {[:parked?] false} unpark-reward))

(def move-base-step-reward -2)

(defn make-base-dir [s [dirname dir]]
  (let [const (state/get-var s :const)
        base  (state/get-var s [:base])
        nbase (add-pos base dir)]
    (when (contains? (get const [:freespace]) nbase)
      (env-util/make-factored-primitive 
       [:base dirname]
       {[:base] base [:parked?] false}
       {[:base] nbase}
       move-base-step-reward))))

(def move-gripper-step-reward -1)

(defn make-gripper-dir [s [dirname dir]]
  (let [const (state/get-var s :const)
        base  (state/get-var s [:base])
        go    (state/get-var s [:gripper-offset])
        ngo   (add-pos go dir)
        npos  (add-pos ngo base)]
    (when (contains? (get const [:legal-go]) ngo)
      (env-util/make-factored-primitive 
       [:gripper dirname]
       {[:base] base [:gripper-offset] go [:parked?] true 
        [:object-at npos] nil}
       {[:gripper-offset] ngo}
       move-gripper-step-reward))))

(def pickup-reward -1)

(defn make-pickup [dirname base go o opos]
  (env-util/make-factored-primitive 
   [:pickup dirname]
   {[:base] base [:gripper-offset] go [:parked?] true 
    [:pos o] opos [:holding] nil [:at-goal? o] false}
   {[:pos o] nil [:holding] o [:object-at opos] nil}
   pickup-reward))

(defn make-pickup-dir [s [dirname dir]]
  (let [base  (state/get-var s [:base])
        go    (state/get-var s [:gripper-offset])
        opos  (add-pos base go dir)
        o     (state/get-var s [:object-at opos])]
    (when (and o (not (= o :border)))
      (make-pickup dirname base go o opos))))

(def putdown-reward -1)

(defn make-putdown [dirname base go o opos]
  (env-util/make-factored-primitive 
       [:putdown dirname]
       {[:base] base [:gripper-offset] go [:parked?] true 
        [:holding] o [:object-at opos] nil}
       {[:pos o] opos [:holding] nil [:object-at opos] o [:at-goal? o] true}
       putdown-reward))

(defn make-putdown-dir [s [dirname dir]]
  (let [const (state/get-var s :const)
        o     (state/get-var s [:holding])
        base  (state/get-var s [:base])
        go    (state/get-var s [:gripper-offset])
        opos  (add-pos base go dir)]
    (when (and o (contains? (get const [:goal o]) opos))
      (make-putdown dirname base go o opos))))


; obstacles are [[minx miny] [maxx maxy]]
; goals are sets os positions.
; objects are [name [cx cy] goal-pos-set] -- no goal means static 
; g-rad is gripper "radius" -- diamond shaped.

; Note, if you pass unreachable goal positions this will suffer.
(defn make-discrete-manipulation-env 
  ([size base obstacles objects g-rad]
     (make-discrete-manipulation-env size base obstacles objects g-rad Integer/MAX_VALUE))
  ([size base obstacles objects g-rad n-base-samples]
     (make-discrete-manipulation-env size base obstacles objects g-rad n-base-samples (make-random 1)))  
  ([size base obstacles objects g-rad n-base-samples #^Random random]
  (let [[width height] size
        border-regions [[[0 0] [0 height]] [[width 0] [width height]]
                        [[0 0] [width 0]] [[0 height] [width height]]]
        border-cells   (set (mapcat region-cells border-regions))
        obstacle-cells (set (mapcat region-cells obstacles))
        all-cells      (set (region-cells [[0 0] size]))
        freespace      (clojure.set/difference all-cells border-cells obstacle-cells)
        legal-go       (set (spiral-to g-rad))]
    (env-util/make-simple-factored-env
     (into {:const (into {[:size] size [:freespace] freespace [:legal-go] legal-go [:objects] objects
                          [:max-go] g-rad
                          [:base-offsets] (pseudo-shuffle random (spiral-to (inc g-rad)) )
                          [:n-base-samples] n-base-samples
;                          [:nav-slack] 1 ; Intentional error in nav/reach descs. >= 1.
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

; (print-state (initial-state (make-discrete-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] #{ [4 4] } ] ] 2)))
; (uniform-cost-search (make-discrete-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] #{ [4 4] } ] ] 2))


;; Same as above, but objects can have goal regions, we'll sample reachable positions.
;; TODO: copy pasta is rather verbose, etc.  
(defn make-discrete-manipulation-env-regions 
  ([size base obstacles objects g-rad n-base-samples n-goal-samples]
     (make-discrete-manipulation-env-regions size base obstacles objects g-rad
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
       (make-discrete-manipulation-env
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

; (uniform-cost-search (make-discrete-manipulation-env-regions [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] [ [4 4] [4 4 ] ] ] ] 2 2 2))

; Make a random env, used in ICAPS'10 poster.
(defn make-random-discrete-manipulation-env [n-objects seed]
  (let [tables [[[3 3] [6 6]] [[13 3] [16 6]] [[3 13] [6 16]] [[13 13] [16 16]]]
        table-positions (apply concat (map region-cells tables))
        random (Random. (long seed))]
    (make-discrete-manipulation-env-regions
     [20 20]
     [1 1]
     tables
     (for [[i start] (util/indexed (take n-objects (pseudo-shuffle random table-positions)))]
       [(keyword (str (char (+ (int \a) i)))) start (nth tables (mod (.nextInt random) 4))])
     1 2 2 (long (+ 17 (* 13 seed))))))

(defn state-map [s]
  (let [const   (state/get-var s :const)
        base    (state/get-var s [:base])
        go      (state/get-var s [:gripper-offset])]
    (reduce (fn [m [[x y] c]] (assoc-in m [y x] c))
            (get const [:map])
            (concat 
             [[(add-pos base go) \G]
              [base              \B]]
             (for [[o] (get const [:objects])
                   :when (state/get-var s [:pos o])]
               [(state/get-var s [:pos o]) (first (name o))])))))

(defn state-str [s]
  (apply str (util/str-join "\n" (map (partial apply str) (state-map s))) "\n"
         (concat (if (state/get-var s [:parked?]) "parked" "unparked") 
                 (if-let [h (state/get-var s [:holding])] [", holding " h "\n"] ["\n"]))))

(defn print-state [s] (print (state-str s)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Hierarchy ;;;;;;;;;;;;;;;;;;;;;

(defn reach-context 
  ([s] (reach-context (state/get-var s :const) (state/get-var s [:base])))
  ([const base]
    (into #{[:base] [:gripper-offset]}
      (for [go (util/safe-get const [:legal-go])]
        [:object-at (add-pos base go)]))))

(defn manhattan-distance [[x1 y1] [x2 y2]]
  (+ (util/abs (- x1 x2)) (util/abs (- y1 y2))))

(defn can-directly-nav-dir? [free-fn cur goal dir]
  (and (free-fn cur)
       (or (= cur goal)
           (can-directly-nav-dir? free-fn (add-pos cur dir) goal dir))))

(defn can-directly-nav? [free-fn [x1 y1 :as l1] [x2 y2 :as l2]]
  (if (< x2 x1) (can-directly-nav? free-fn l2 l1)
      (and (can-directly-nav-dir? free-fn l1 [x2 y1] [-1 0])
           (can-directly-nav-dir? free-fn [x2 y1] l2 [0 (util/signum (- y2 y1))]))))

(defn can-reach-from? [const dst-go] (contains? (const [:legal-go]) dst-go))


(defn can-span? [const l1 l2]
  (<= (manhattan-distance l1 l2)
      (+ 2 (* 2 (get const [:max-go])))))

(defn move-gripper-reward [src dst] (* move-gripper-step-reward (manhattan-distance src dst)))

;(defn reach-refinements [cur-go dst-go])

(defn make-reach-hla [const dst-go] 
  (when (can-reach-from? const dst-go)
    (reify 
     env/Action
     (action-name [_] [:reach dst-go])
     (primitive?  [_] false)

     env/ContextualAction
     (precondition-context [_ s] (reach-context s))

     hierarchy/HighLevelAction
     (immediate-refinements- [this s]
       (if (= dst-go (state/get-var s [:gripper-offset]))
         [[]]
         (for [dir dirs :let [a (make-gripper-dir s dir)] :when a] 
           [a this])))
     (cycle-level-           [_ s] 1)

     angelic/ExplicitAngelicAction
     (optimistic-map-  [_ s]
       (when-not (state/get-var s [:object-at (add-pos (state/get-var s [:base]) dst-go)])
         {(state/set-var s [:gripper-offset] dst-go)
          (move-gripper-reward (state/get-var s [:gripper-offset]) dst-go)}))
     (pessimistic-map- [_ s]
       (let [base (state/get-var s [:base])
             go   (state/get-var s [:gripper-offset])]
         (if (can-directly-nav? 
              #(not (state/get-var s [:object-at (add-pos base %)]))
              go dst-go)
           {(state/set-var s [:gripper-offset] dst-go)
            (move-gripper-reward go dst-go)}
           {})))

     angelic/ImplicitAngelicAction 
     (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
     (can-refine-from-set? [a ss] (state-set/vars-known? ss [[:gripper-offset]]))
     (immediate-refinements-set- [a ss]
       (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))]
         [{[:object-at (add-pos (state-set/get-known-var ss [:base]) dst-go)] #{nil}} p]))
     (optimistic-set-and-reward- [a ss]
       (assert (state-set/vars-known? ss [[:base]]))
       (let [dst-pos (add-pos (state-set/get-known-var ss [:base]) dst-go)
             con-ss  (state-set/constrain ss {[:object-at dst-pos] #{nil}})]
         (when-not (state-set/empty? con-ss)
           [(state/set-var con-ss [:gripper-offset] #{dst-go})
            (apply max (for [cgo (state/get-var con-ss [:gripper-offset])]
                         (move-gripper-reward cgo dst-go)))])))
     (pessimistic-set-and-reward- [a ss] ::TODO))))


(defn possible-grasp-gos [const base pos]
  (for [[dirname dir] dirs
        :let [go (sub-pos (sub-pos pos dir) base)]
        :when (can-reach-from? const go)]
    go))

(defn possible-grasp-gos-ss [const bases pos]
  (set (apply concat (for [base bases] (possible-grasp-gos const base pos)))))

;; TODO: slack? pess? 
(defn make-grasp-hla [o] 
 (reify
  env/Action
  (action-name [_] [:grasp o])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] (conj (reach-context s) [:pos o] [:at-goal? o] [:holding]))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [const (state/get-var s :const)
          base (state/get-var s [:base])
          opos (state/get-var s [:pos o])]
      (for [[dirname dir] dirs
            :let [gpos (sub-pos opos dir)
                  go   (sub-pos gpos base)
                  a    (make-reach-hla const go)]
            :when a]
        [a (make-pickup dirname base go o opos)])))
  (cycle-level-           [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map-  [_ s]
    (let [opos (state/get-var s [:pos o])]
      (into {}
            (for [go (possible-grasp-gos (state/get-var s :const) (state/get-var s [:base]) opos)]
              [(state/set-vars s [[[:gripper-offset] go]
                                  [[:pos o] nil] [[:holding] o]
                                  [[:object-at opos] nil]])
               (+ pickup-reward
                  (move-gripper-reward (state/get-var s [:gripper-offset]) go))]))))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
   (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))][{} p]))
  (optimistic-set-and-reward- [a ss]
    (assert (state-set/vars-known? ss [[:base] [:gripper-offset] [:pos o]]))
    (let [opos (state-set/get-known-var ss [:pos o])
          base (state-set/get-known-var ss [:base])
          cgo  (state-set/get-known-var ss [:gripper-offset])
          gos  (set (possible-grasp-gos (state-set/get-known-var ss :const) base opos))]
      [(state/set-vars ss [[[:gripper-offset] gos]
                           [[:pos o] #{nil}] [[:holding] #{o}]
                           [[:object-at opos] #{nil}]])
       (+ pickup-reward
          (apply max (for [go gos] (move-gripper-reward cgo go))))]))
  (pessimistic-set-and-reward- [a ss] nil)))

(defn drop-reward [base init-go o-dst]
  (let [rel-o-dst (sub-pos o-dst base)]
    (+ putdown-reward
       (min (move-gripper-reward init-go [0 0])
            (+ (move-gripper-reward init-go rel-o-dst)
               (move-gripper-reward rel-o-dst [0 0])
               (* -2 move-gripper-step-reward))))))


(defn drop-reward-ss [base init-gos o-dst]
  (apply max (for [go init-gos] (drop-reward base go o-dst))))

;; TODO: slack, pess ?
(defn make-drop-at-hla [o dst]
 (reify 
  env/Action
  (action-name [_] [:drop-at o dst])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] (conj (reach-context s) [:holding] [:object-at dst]))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [const (state/get-var s :const)
          base (state/get-var s [:base])]
      (for [[dirname dir] dirs
            :let [gpos (sub-pos dst dir)
                  go   (sub-pos gpos base)
                  a    (make-reach-hla const go)]
            :when a]
        [a (make-putdown dirname base go o dst) (make-reach-hla const [0 0])])))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    {(state/set-vars s [[[:gripper-offset] [0 0]]
                        [[:pos o] dst] [[:holding] nil]
                        [[:object-at dst] o] [[:at-goal? o] true]])
     (drop-reward (state/get-var s [:base])
                  (state/get-var s [:gripper-offset]) dst )})
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
   (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (assert (state-set/vars-known? ss [[:base]]))
    [(state/set-vars ss [[[:gripper-offset] #{[0 0]}]
                         [[:pos o] #{dst}] [[:holding] #{nil}]
                         [[:object-at dst] #{o}] [[:at-goal? o] #{true}]])
     (drop-reward-ss (state-set/get-known-var ss [:base]) (state/get-var ss [:gripper-offset]) dst)])
  (pessimistic-set-and-reward- [a ss] nil)))

;manhattan
;pess: SLD?  



(defn nav-reward [src dst] (* move-base-step-reward (manhattan-distance src dst)))

;; TODO: should nav be done by external alg, (fairest between angelic/not) or explicit? 
(defn make-nav-hla [dst] 
 (reify
  env/Action
  (action-name [_] [:nav dst])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{[:base]})

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (if (= dst (state/get-var s [:base]))
      [[]]
      (for [dir dirs :let [a (make-base-dir s dir)] :when a]
        [a this])))
  (cycle-level- [_ s] 1)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    {(state/set-var s [:base] dst)
     (nav-reward (state/get-var s [:base]) dst)})
  (pessimistic-map- [_ s]
     (let [cbase (state/get-var s [:base])]
       (if (can-directly-nav?
            (let [fs ((state/get-var s :const) [:freespace])]
              #(contains? fs %))
            cbase dst)
         {(state/set-var s [:base] dst)
          (nav-reward cbase dst)}
         {})))

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a :dummy))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (assert (state-set/vars-known? ss [[:base]]))                              
    [(state/set-var ss [:base] #{dst})
     (nav-reward (state-set/get-known-var ss [:base]) dst)])
  (pessimistic-set-and-reward- [a ss] ::TODO)))
; manhattan
; pess? SLD? (try direct line, if occ then -inf).

(defn move-base-reward [src dst cgo]
  (if (= src dst) 0 
    (+ park-reward unpark-reward 
       (move-gripper-reward cgo [0 0])
       (nav-reward src dst))))



(defn make-move-base-hla [dst]
 (reify 
  env/Action
  (action-name [_] [:move-base dst])
  (primitive?  [_] false)

  env/ContextualAction
  (precondition-context [_ s] #{[:base] [:parked?] [:gripper-offset]})

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (let [base (state/get-var s [:base])]
      (if (= base dst)
        [[]]
        [[(make-reach-hla (state/get-var s :const) [0 0]) (make-unpark s) 
          (make-nav-hla dst) (make-park s)]])))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (let [base (state/get-var s [:base])]
      (if (= base dst)
        {s 0}
        {(state/set-vars s [[[:base] dst] [[:gripper-offset] [0 0]]])
         (move-base-reward (state/get-var s [:base]) dst (state/get-var s [:gripper-offset]))})))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a :dummy))  
  (can-refine-from-set? [a ss] (state-set/vars-known? ss [[:base]]))
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss]
    (let [srcs (state/get-var ss [:base])
          cgos (state/get-var ss [:gripper-offset])
          must-move? (not (contains? srcs dst))]
      [(state/set-vars ss [[[:base] #{dst}] [[:gripper-offset] (if must-move? #{[0 0]} (conj cgos [0 0]))]])
       (if must-move?
         (+ park-reward unpark-reward
            (apply max (for [src srcs] (nav-reward src dst)))
            (apply max (for [cgo cgos] (move-gripper-reward cgo [0 0]))))
         0)]))
  (pessimistic-set-and-reward- [a ss] nil)))

;                              (let [base (state/get-var s [:base])
;                                    fs ((state/get-var s :const) [:freespace])]
;                                (if (can-directly-nav? fs base dst)
;                                  {(state/set-var s [:base] dst)
;                                   (move-base-reward base dst)}
;                                  {}))



;; Note: since we may not sample current position, have to special case.
(defn possible-grasp-base-pos 
  ([s grasp-pos] 
     (possible-grasp-base-pos (state/get-var s :const) (state/get-var s [:base]) grasp-pos))
  ([const base grasp-pos]
;     (println "pgbp" base grasp-pos)
     (let [free  (get const [:freespace])
           candidates (->> (get const [:base-offsets])
                           (map #(add-pos % grasp-pos))
                           (filter free))]
       (if (some #{base} candidates)
         (cons base (remove #{base} (take (get const [:n-base-samples]) candidates)))
         (take (get const [:n-base-samples]) candidates)))))

(defn possible-grasp-base-pos-ss
  ([const bases grasp-pos]
     (let [free  (get const [:freespace])
           candidates (->> (get const [:base-offsets])
                           (map #(add-pos % grasp-pos))
                           (filter free))]
       (if (some bases candidates)
         [(util/intersection-coll bases candidates) (set (take (inc (get const [:n-base-samples])) candidates))]
         [nil                                       (set (take (get const [:n-base-samples]) candidates))]))))


;; TODO: pess
(defn make-go-grasp-hla [o] 
 (reify
  env/Action
  (action-name [_] [:go-grasp o])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] -
    (conj (reach-context (state/get-var s :const) (state/get-var s [:pos o])) 
          [:pos o] [:at-goal? o] [:holding]))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (for [dst (possible-grasp-base-pos s (state/get-var s [:pos o]))]
      [(make-move-base-hla dst) (make-grasp-hla o)]))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (let [base (state/get-var s [:base])
          opos (state/get-var s [:pos o])]
      (into {}
            (for [dst (possible-grasp-base-pos s opos),
                  go  (possible-grasp-gos (state/get-var s :const) dst opos)]
              [(state/set-vars s [[[:base] dst]
                                  [[:gripper-offset] go]
                                  [[:pos o] nil] [[:holding] o]
                                  [[:object-at opos] nil]])
               (+ (move-base-reward base dst [0 0])
                  (move-gripper-reward
                   (if (= base dst) (state/get-var s [:gripper-offset]) [0 0])
                   go)
                  pickup-reward)]))))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (let [const (state-set/get-known-var ss :const)
          bases (state/get-var ss [:base])
          opos  (state-set/get-known-var ss [:pos o])
          [stays goes] (possible-grasp-base-pos-ss const bases opos)
          stayonlys (clojure.set/difference stays goes)]
      (concat
       (for [b stayonlys] [{[:base] #{b}} [(make-move-base-hla b) (make-grasp-hla o)]])
       (for [b goes]      [{}          [(make-move-base-hla b) (make-grasp-hla o)]]))))
  (optimistic-set-and-reward- [a ss]
    (let [const (state-set/get-known-var ss :const)
          bases (state/get-var ss [:base])
          cgos  (state/get-var ss [:gripper-offset])
          opos  (state-set/get-known-var ss [:pos o])
          [stays goes] (possible-grasp-base-pos-ss const bases opos)
          allbases  (clojure.set/union stays goes)
          gos       (possible-grasp-gos-ss const allbases opos)]
      [(state/set-vars ss [[[:base] allbases] [[:gripper-offset] gos]
                           [[:pos o] #{nil}] [[:holding] #{o}] [[:object-at opos] #{nil}]])
       (+ pickup-reward
          (apply max
            (+ (apply max (for [go cgos] (move-gripper-reward go [0 0])))
               park-reward unpark-reward
               (let [d (dec (apply min (for [base bases] (manhattan-distance base opos))))
                     max-go (util/safe-get const [:max-go])
                     gd     (min d max-go)]
                 (+ (* move-gripper-step-reward gd)
                    (* move-base-step-reward (- d gd)))))
            (for [stay stays, go cgos]
              (* move-gripper-step-reward (max 0 (dec (manhattan-distance (add-pos stay go) opos)))))))]))
  (pessimistic-set-and-reward- [a ss] nil)
  ))

(defn go-drop-at-opt [s o o-dst]
  (let [base (state/get-var s [:base])
        go   (state/get-var s [:gripper-offset])]
    (into {}
        (for [dst (possible-grasp-base-pos s o-dst)]
          [(state/set-vars s [[[:base] dst]
                            [[:gripper-offset] [0 0]]
                            [[:pos o] o-dst] [[:holding] nil]
                            [[:object-at o-dst] o] [[:at-goal? o] true]])
             (+ (move-base-reward base dst go)
                (if (= base dst)
                   (drop-reward dst go o-dst)
                   (drop-reward dst [0 0] o-dst)))]))))

;; Note: since we may not sample current position, have to special case.
(defn make-go-drop-at-hla [o o-dst] 
 (reify 
  env/Action
  (action-name [_] [:go-drop-at o o-dst])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s]
    (conj (reach-context (state/get-var s :const) o-dst) [:holding] [:object-at o-dst]))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (for [dst (possible-grasp-base-pos s o-dst)]
      [(make-move-base-hla dst) (make-drop-at-hla o o-dst)]))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s] (go-drop-at-opt s o o-dst))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (let [const (state-set/get-known-var ss :const)
          bases (state/get-var ss [:base])
          [stays goes] (possible-grasp-base-pos-ss const bases o-dst)
          stayonlys (clojure.set/difference stays goes)]
      (concat
       (for [b stayonlys] [{[:base] #{b}} [(make-move-base-hla b) (make-drop-at-hla o o-dst)]])
       (for [b goes]      [{}          [(make-move-base-hla b) (make-drop-at-hla o o-dst)]]))))
  (optimistic-set-and-reward- [a ss]
    (let [const (state-set/get-known-var ss :const)
          bases (state/get-var ss [:base])
          cgos  (state/get-var ss [:gripper-offset])
          [stays goes] (possible-grasp-base-pos-ss const bases o-dst)
          allbases  (clojure.set/union stays goes)
;          gos       (possible-grasp-gos-ss const allbases o-dst)
          ]
      [(state/set-vars ss [[[:base] allbases] [[:gripper-offset] #{[0 0]}]
                           [[:pos o] #{o-dst}] [[:holding] #{nil}] [[:object-at o-dst] #{o}]])
       (+ putdown-reward
          (apply max
            (+ (apply max (for [go cgos] (move-gripper-reward go [0 0])))
               park-reward unpark-reward
               (let [d (dec (apply min (for [base bases] (manhattan-distance base o-dst))))
;                     max-go (util/safe-get const [:max-go])
;                     gd     (min d max-go)
                     ]
                 (assert (= (* 2 move-gripper-step-reward) move-base-step-reward ))
                 (* move-base-step-reward d)))
            (for [stay stays, go cgos]
              (* move-gripper-step-reward (max 0 (dec (manhattan-distance (add-pos stay go) o-dst)))))))]))
  (pessimistic-set-and-reward- [a ss] nil)
  ))


(defn make-go-drop-hla [o] 
 (reify
  env/Action
  (action-name [_] [:go-drop o])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] 
    (conj (apply clojure.set/union 
                 (map #(conj (reach-context (state/get-var s :const) %) [:object-at %]) 
                      (get (state/get-var s :const) [:goal o]))) 
          [:holding]))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s]
    (for [o-dst (util/safe-get (state/get-var s :const) [:goal o])
          :when (not (state/get-var s [:object-at o-dst]))]
      [(make-go-drop-at-hla o o-dst)]))
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    (reduce util/merge-disjoint
            (map #(go-drop-at-opt s o %)
                 (get (state/get-var s :const) [:goal o]))))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction 
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [o-dst (get (state-set/get-known-var ss :const) [:goal o])]
      [{[:object-at o-dst] #{nil}} [(make-go-drop-at-hla o o-dst)]]))
  (optimistic-set-and-reward- [a ss]
    ;; Cost = if possible stay, min dist from gripper to drop loc.  
    ;; Otherwise, min dist to a dst. 
    (let [const (state-set/get-known-var ss :const)
          dsts  (util/safe-get const [:goal o])
          bases (state/get-var ss [:base])
          cgos  (state/get-var ss [:gripper-offset])
          sgs   (for [o-dst dsts] (possible-grasp-base-pos-ss const bases o-dst))
          stays (apply clojure.set/union (map first sgs))
          goes  (apply clojure.set/union (map second sgs))          
          allbases  (clojure.set/union stays goes)]
      (assert (seq dsts))
      [(state/set-vars ss (concat [[[:base] allbases] [[:gripper-offset] #{[0 0]}]
                                   [[:pos o] dsts] [[:holding] #{nil}]]
                                  (if-let [s (util/singleton dsts)]
                                    [[[:object-at s] #{o}]]
                                    (for [o-dst dsts]
                                      [[:object-at o-dst] #{o nil}]))))
       
       (+ putdown-reward
          (apply max
            (+ (apply max (for [go cgos] (move-gripper-reward go [0 0])))
               park-reward unpark-reward
               (let [d (dec (apply min (for [base bases, o-dst dsts] (manhattan-distance base o-dst))))]
                 (assert (= (* 2 move-gripper-step-reward) move-base-step-reward ))
                 (* move-base-step-reward d)))
            (for [stay stays, go cgos, o-dst dsts]
              (* move-gripper-step-reward (max 0 (dec (manhattan-distance (add-pos stay go) o-dst)))))))]))
  (pessimistic-set-and-reward- [a ss] nil)
))

(defn move-to-goal-context [s o]
  (conj (apply clojure.set/union 
               (map #(conj (reach-context (state/get-var s :const) %) [:object-at %]) 
                    (cons (state/get-var s [:pos o])
                          (get (state/get-var s :const) [:goal o])))) 
        [:holding]))

(defn move-to-goal-opt [s o]
;  (println "\n\n")
  (assert (= (state/get-var s [:gripper-offset]) [0 0]))
  (let [const (state/get-var s :const)
        base (state/get-var s [:base])
        o-pos (state/get-var s [:pos o])]
    (reduce util/merge-disjoint
            (for [o-dst (get const [:goal o])]
              (apply merge-with max
                     (for [b-med (possible-grasp-base-pos const base o-pos)
                           b-dst (possible-grasp-base-pos const b-med o-dst)
                           :let [rel-src (sub-pos o-pos b-med)
                                 rel-dst (sub-pos o-dst b-dst)
                                        ;_ (println o-dst base b-med b-dst rel-src rel-dst)
                                 ]
                           ]
                       {(state/set-vars s [[[:base] b-dst] [[:pos o] o-dst] 
                                         [[:object-at o-pos] nil] [[:object-at o-dst] o]
                                         [[:at-goal? o] true]])
                        (+ (move-base-reward base b-med [0 0])
                           (move-base-reward b-med b-dst [0 0])
                           pickup-reward putdown-reward
                           (if (= b-med b-dst)
                             (min 0 (+ (move-gripper-reward [0 0] rel-src)
                                       (move-gripper-reward rel-src rel-dst)
                                       (move-gripper-reward rel-dst [0 0])
                                       (* -4 move-gripper-step-reward)))
                             (+ (min 0 (+ (* 2 (move-gripper-reward [0 0] rel-src))
                                          (* -2 move-gripper-step-reward)))
                                (min 0 (+ (* 2 (move-gripper-reward [0 0] rel-dst))
                                          (* -2 move-gripper-step-reward))))))}))))))



;; TODO: cache as much as this as we can ?
(defn make-move-to-goal-hla [o] 
 (reify 
  env/Action
  (action-name [_] [:move-to-goal o])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] (move-to-goal-context s o))

  hierarchy/HighLevelAction
  (immediate-refinements- [_ s] [[(make-go-grasp-hla o) (make-go-drop-hla o)]])
  (cycle-level- [_ s] nil)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s] #_ (println (util/map-keys state-str (move-to-goal-opt s o))) (move-to-goal-opt s o))
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction
  (precondition-context-set [a ss] (env/precondition-context a (state-set/some-element ss)))  
  (can-refine-from-set? [_ ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [_ ss]
    (let [const (state-set/get-known-var ss :const)
          sbases (state/get-var ss [:base])
          sgos   (state/get-var ss [:gripper-offset])
          o-src  (state-set/get-known-var ss [:pos o])
          o-dsts (util/safe-get const [:goal o])
          [mstays mgoes] (possible-grasp-base-pos-ss const sbases o-src)
          allmbases      (clojure.set/union mstays mgoes)
          fsgs   (for [o-dst o-dsts] (possible-grasp-base-pos-ss const allmbases o-dst))
          fstays (apply clojure.set/union (map first fsgs))
          fgoes  (apply clojure.set/union (map second fsgs))          
          allfbases  (clojure.set/union fstays fgoes)
          bothstays     (clojure.set/intersection mstays fstays)]
      (assert (= (seq sgos) [[0 0]]))
      [(state/set-vars ss (concat [[[:base] allfbases] [[:gripper-offset] #{[0 0]}]
                                   [[:pos o] o-dsts] [[:holding] #{nil}]]
                                  (if-let [s (util/singleton o-dsts)]
                                    [[[:object-at s] #{o}]]
                                    (for [o-dst o-dsts] [[:object-at o-dst] #{o nil}]))))       
       (+ pickup-reward putdown-reward
          (apply max
           (concat
            ; no base movement
            (for [base bothstays, go sgos, o-dst o-dsts]
              (* move-gripper-step-reward
                 (+ (max 0 (- (manhattan-distance go o-src) 1))
                    (max 0 (- (manhattan-distance o-src o-dst) 2))
                    (max 0 (- (manhattan-distance o-dst base) 1)))))

            ; no first base movement
            (for [mbase mstays, fbase allfbases, go sgos, o-dst o-dsts]
              (+ park-reward unpark-reward
                 (* move-base-step-reward (manhattan-distance mbase fbase))
                 (* move-gripper-step-reward
                    (+ (max 0 (- (manhattan-distance go o-src) 1))
                       (max 0 (- (manhattan-distance o-src mbase) 1))
                       (* 2 (max 0 (- (manhattan-distance fbase o-dst) 1)))))))

            ; no second base movement
            (for [sbase sbases, fbase fstays, go sgos, o-dst o-dsts]
              (+ park-reward unpark-reward
                 (* move-base-step-reward (manhattan-distance sbase fbase))
                 (* move-gripper-step-reward
                    (+ (manhattan-distance go [0 0])
                       (max 0 (- (manhattan-distance fbase o-src) 1))
                       (max 0 (- (manhattan-distance o-src o-dst) 2))                       
                       (max 0 (- (manhattan-distance o-dst fbase) 1))))))

            ; both base movements -- TODO: speed up ?
            (for [sbase sbases, mbase allmbases, fbase allfbases, go sgos, o-dst o-dsts]
              (+ (move-base-reward sbase mbase go)                 
                 (move-base-reward sbase mbase [0 0])
                 (* move-gripper-step-reward
                    (* 2 (max 0 (- (manhattan-distance mbase o-src) 1)))
                    (* 2 (max 0 (- (manhattan-distance fbase o-dst) 1)))))))))]))
  (pessimistic-set-and-reward- [_ ss] nil)))

(defn remaining-objects [s] 
  (remove #(state/get-var s [:at-goal? %])
          (map first (get (state/get-var s :const) [:objects]))))

; reward to get from current base position to gripper-in-grasp-position
(defn start-reward [s o]
  (let [const (state/get-var s :const)
        max-go (util/safe-get const [:max-go])
        base (state/get-var s [:base])
        o-pos (state/get-var s [:pos o])
        dist   (dec (manhattan-distance base o-pos))]
    (if (<= dist max-go)
        (* move-gripper-step-reward dist)
      (+ unpark-reward park-reward (* (- dist max-go) move-base-step-reward)
         (* move-gripper-step-reward max-go)))))

(defn start-reward-ss [ss o]
  (let [const  (state-set/get-known-var ss :const)
        max-go (util/safe-get const [:max-go])
        bases  (state/get-var ss [:base])
        o-pos  (state-set/get-known-var ss [:pos o])
        dist   (dec (apply min (for [base bases] (manhattan-distance base o-pos))))]
    (if (<= dist max-go)
        (* move-gripper-step-reward dist)
      (+ unpark-reward park-reward (* (- dist max-go) move-base-step-reward)
         (* move-gripper-step-reward max-go)))))

; reward to get from some dropoff base position of o1 to gripper-in-grasp-position for o2.
(defn linkage-reward [s o1 o2]
  (let [const    (state/get-var s :const)
        max-go   (util/safe-get const [:max-go])
        o1-goals (util/safe-get const [:goal o1])
        o2-pos   (state/get-var s [:pos o2])        
        dist     (apply min (map #(manhattan-distance % o2-pos) o1-goals))]
    (if (<= dist (+ 2 (* 2 max-go)))
        (* move-gripper-step-reward (max 0 (- dist 2)))
      (+ unpark-reward park-reward (* (- dist (+ 2 (* 2 max-go))) move-base-step-reward)
         (* move-gripper-step-reward (* 2 max-go))))))

; reward for gripper-in-grasp-position to object at goal, gripper at home.
;; TODO: tighten this up?  right now, missing to-home part.
(defn object-reward [s o]
  (let [const   (state/get-var s :const)
        max-go  (util/safe-get const [:max-go])
        o-pos   (state/get-var s [:pos o])
        goals   (util/safe-get const [:goal o])
        dist    (apply min (map #(manhattan-distance % o-pos) goals))]
    (+ pickup-reward putdown-reward
     (if (<= dist (+ 2 (* 2 max-go)))
       (* move-gripper-step-reward (max 0 (- dist 2)))
       (+ unpark-reward park-reward (* (- dist (+ 2 (* 2 max-go))) move-base-step-reward)
          (* move-gripper-step-reward (* 2 max-go)))))))


(defn compute-match-edges
  "Compute edges, except for start, for matching.  Each edge represents a bound on the reward to deliver the
   second object, starting from a state just after the first object has been delivered.  :end represents
   the reward to get to the final configuration, with the gripper home."
  [s object-rewards]
  (concat 
   (for [[o1] object-rewards, [o2 or] object-rewards :when (not (= o1 o2))]
       [o1 o2 (+ or (linkage-reward s o1 o2))])
   (for [[o] object-rewards] [o :finish 0])))

;; TODO: can do better on context -- but probably rarely matters?
(defn- make-tla [env]
 (let [init    (env/initial-state env)
       finish  (env-util/make-finish-goal-state env)
       finish-set (util/map-vals (fn [x] #{x}) finish)
       context (util/keyset (dissoc init :const))
       objects (remaining-objects init)
       object-rewards (into {} (for [o objects] [o (object-reward init o)]))
       match-edges (compute-match-edges init object-rewards)]
 (reify
  env/Action
  (action-name [_] [:discretem-tla])
  (primitive? [_] false)

  env/ContextualAction
  (precondition-context [_ s] context)

  hierarchy/HighLevelAction
  (immediate-refinements- [this s]
    (let [remaining (remaining-objects s)]
      (if (empty? remaining)
        [[(env-util/make-finish-action env)]]
        (for [o remaining] [(make-move-to-goal-hla o) this]))))
  (cycle-level- [_ s] 2)

  angelic/ExplicitAngelicAction
  (optimistic-map- [_ s]
    {(state/set-vars s finish)
     (let [objects (remaining-objects s), 
           s1 (set (cons :start objects)), 
           s2 (set (cons :finish objects))]
       (if (empty? objects ) 0
           (util/maximum-matching s1 s2 
             (concat (for [o objects] [:start o (+ (object-rewards o) (start-reward s o))])
                     (filter (fn [[n1 n2]] (and (s1 n1) (s2 n2))) match-edges)))))})
  (pessimistic-map- [_ s] {})

  angelic/ImplicitAngelicAction
  (precondition-context-set [a ss] context)  
  (can-refine-from-set? [a ss] true)
  (immediate-refinements-set- [a ss]
    (for [p (hierarchy/immediate-refinements- a (state-set/some-element ss))] [{} p]))
  (optimistic-set-and-reward- [a ss] ;; Same as explicit, except start-reward-ss.
    [(state/set-vars ss finish-set)
     (let [some-s  (state-set/some-element ss)
           objects (remaining-objects some-s), 
           s1 (set (cons :start objects)), 
           s2 (set (cons :finish objects))]
       (if (empty? objects) 0
           (util/maximum-matching s1 s2 
             (concat (for [o objects] [:start o (+ (object-rewards o) (start-reward-ss ss o))])
                     (filter (fn [[n1 n2]] (and (s1 n1) (s2 n2))) match-edges)))))])
  (pessimistic-set-and-reward- [a ss] nil))))

(defn make-discrete-manipulation-hierarchy [env]
  (hierarchy-util/make-simple-hierarchical-env env [(make-tla env)]))


; (use '[angelic discrete-manipulation env hierarchy hierarchical-incremental-search] 'edu.berkeley.ai.util)

; (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1)
; (print-state (initial-state (make-discrete-manipulation-env [10 10] [1 1] [ [ [4 4] [6 6] ] ] [ [:a [5 5] [ [4 4] [4 4] ] ] ] 2))) 

; (sahucs-flat )

; (let [e (make-discrete-manipulation-env-regions [10 10] [1 1] [ [ [4 4] [7 7] ] ] [ [:a [5 5] [ [4 4] [4 4 ] ] ] ] 1 2 2 1) h (make-discrete-manipulation-hierarchy e)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(sahucs-flat h)))))

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]] [:d [5 15] [[4 4] [7 7]]]] 1 2 2 1) h (make-discrete-manipulation-hierarchy e)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(sahucs-flat h)))) (println (time (run-counted #(sahucs-inverted h)))))

;  (let [e (make-discrete-manipulation-env-regions [4 4] [1 1] [ [ [2 2] [3 3] ] ] [ [:a [2 2] [ [3 3] [3 3 ] ] ] ] 1 2 2 1) h (make-discrete-manipulation-hierarchy e)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(sahucs-inverted h)))) (println (time (run-counted #(saha-simple h)))))

; (let [e (make-discrete-manipulation-env-regions [10 10] [1 1] [ [ [4 4] [7 7] ] ] [ [:a [5 5] [ [4 4] [4 4 ] ] ] ] 1 2 2 1) h (make-discrete-manipulation-hierarchy e)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(saha-simple h)))))

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)] (println (time (run-counted #(uniform-cost-search e)))) (println (time (run-counted #(sahucs-inverted h))))  (println (time (run-counted #(saha-simple h))))) 

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]  [:d [5 15] [[4 4] [7 7]]] [:e [6 15] [[14 14] [17 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)]   (println (time (run-counted #(saha-simple h)))))

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]  [:d [5 15] [[4 4] [7 7]]] [:e [6 6] [[14 14] [17 17]]] [:f [15 6] [[4 14] [7 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)]   (println (time (run-counted #(saha-simple h)))))

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]  [:d [5 15] [[4 4] [7 7]]] [:e [6 6] [[14 14] [17 17]]] [:f [15 6] [[4 14] [7 17]]]  [:g [16 6] [[4 14] [7 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)]   (println (time (run-counted #(saha-simple h)))))





;  (let [e (make-discrete-manipulation-env-regions [7 4] [1 1] [[[2 2] [3 3]] [[5 2] [6 3]] ]  [[:a [2 2] [[5 2] [6 3]]] [:b [5 2] [[2 2] [3 3]]]] 1 2 2 1) h (make-discrete-manipulation-hierarchy e)]  (println (time (run-counted #(saha-simple h)))) (println (time (run-counted #(aha-star-simple h)))))

;(let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)] (doseq [[an alg] aaai-algs] (println an (time (run-counted #(alg h))))))

; (let [e (make-discrete-manipulation-env-regions [20 20] [1 1] [[[4 4] [7 7]] [[4 14] [7 17]] [[14 4] [17 7]] [[14 14] [17 17]]]  [[:a [5 5] [[14 4] [17 7]]] [:b [15 5] [[14 14] [17 17]]] [:c [15 15] [[4 14] [7 17]]]   [:d [5 15] [[4 4] [7 7]]] [:e [6 6] [[14 14] [17 17]]] [:f [15 6] [[4 14] [7 17]]]] 1 2 2 1)  h (make-discrete-manipulation-hierarchy e)] (doseq [[an alg] (take-last 3 aaai-algs)] (println an (time (run-counted #(alg h))))))

