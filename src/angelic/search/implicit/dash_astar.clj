(ns angelic.search.implicit.dash-astar
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList]))

;; A revampting of dash_astar_opt, to move subsumption relationships and caching
;; out into a separate class.  This is necessary to keep pessimistic and optimistic
;; things in sync, and should help simplify and generalize subsumption stuff.

;; All TODOs from dash_astar_opt also apply here.

;; TODO: Split out SP "name" from stub
;; TODO: SP has hash table from (state-abstracted context) input set to stub (?).
;; TODO: stub has link back to parent SP
;; TODO: How are subsumption links handled?  
;; What if we create tree summarizer with stub ? ? ?   ?  ?? ? ?  ?  ? ?

;; TODO: add pess

;; TODO: propagate top-down-bounds downward in smarter way using existing IS?
;; TODO: we need to make sure tree sums get called on add-output! first to ensure
;;       consistency with top-down-bounds ? 
;; TODO: top-down bound business does not actually help at all

;;  (except ensuring consistency if we're asserting it...)
;; When we create a stub, we also get: tree summarizer, subsumption-thing.
;; (subsumption-children are parent tree-summarizers).
;; Subsumption-thing is subsumption-child of stub, summarizer, tree-summarizer.
;; Tree-summarizers also remember best bound, this gives us consistency
;; How do they pass to children, though?
;; Apparent cycle -- tree summarizer has children that are child tree-summarizers,
;; And, these children should have the parent TS as a subsumption child.
;; Key: this is only to preserve info from original SP, subsumption..
;; This info should go into subsumption-thing.
;; Subsumption-thing is just ordinary max over children, + self, + TS?
;; ->>(We rely on eager updates to make sure it gets updated?)

;; TDB should not actually go into TS, children should be directly bounded?
;; All children, including inner SP, should do it fine.
;; This means that every thing has exactly one subsumption parent ... which is nice.
;; How does consistency get approached ?
;; We just have the cycle, but would be great if we didn't have to go in child --> ts --> st --> children
;; cycle every time things to up -- maybe ST just doesn't update ord. parents.
;; TODO: figure this out later. 


;; Can goall the way down to nearest sum, I guess...
;; Subsumer gets attached to subsumer of any child (or inner child?)

;; What do we do about multiple ways to express a given plan ? ? ? ?
;; Can normalize or not, interesting question... start without. 


(set! *warn-on-reflection* true)

(def *left-recursive*        true) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(def *collect-equal-outputs* true) ;; Collect identical output sets
(def *decompose-cache*       true) ;; nil for none, or bind to hashmap
(def *state-abstraction*     :eager ) ;; Or lazy or nil.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Watches      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stubs have at most one output (SP), SPs have any number

(defprotocol Watched
  (add-watcher! [s w] "Add a watcher to be notified of all outputs to this.
                       A watcher is just a fn of new-subproblem.")
  (add-output!  [sw o] "O is a subproblem.  sw may have an updated summary,
                        but will not call summary-changed! on its parents.
                        The receiver is responsible for handling this change.
                        This allows handling decrease+increase in lock-step. ")
  (get-outputs  [sw]  "List current outputs"))

(def *out-count* (atom 1))

(traits/deftrait watched-node
  []
  [^ArrayList watchers (ArrayList.)
   ^ArrayList outputs (ArrayList.)]
  [summaries/simple-cached-node]
  Watched
  (add-watcher! [sw w] #_(println :AW sw w) 
    (.add watchers w) 
    (doseq [o (doall (seq outputs))] (swap! *out-count* inc) (w o)) )
  (add-output! [sw o] ;               (println :AO sw o) (Thread/sleep 10)
    (.add outputs o)
    (doseq [w (doall (seq watchers))] (swap! *out-count* inc) (w o)))
  (get-outputs [sw] (doall (seq outputs))))

(defn- connect-and-watch! [p c f]
  (summaries/connect! p c false)
  (add-watcher! c f))

;;;;;;;;;;;;;;;;;;;;;;;;;;      Tree Summarizers      ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every child of TS is also a subsumption parent.
;; Then, TS has:
;; Children:
;;  Ordinary: stub, SP, TS of outputs
;;  Subsuming: Subsuming TS's
;; Parents:
;;  Ordinary: whoever
;;  Subsuming: stub, SP, TS of outputs,
;; Note alternative: separate TS and ST - -but cycle is needed for memory, no matter what?.

(declare sp-ts get-stub-output)

;; Note: at least duriung creation, cycles *are* actually vicious -- lead to StackOverflow.
;; TODO: fix cycles by making subsumption updates only happen when strictly < reward.
;; TODO: what updates are needed here?
(defn- make-tree-summarizer [stub]
  (let [bound-atom (atom 0)
        ret (traits/reify-traits [summaries/simple-cached-node]
              summaries/Summarizable
              (summarize [s] 
                (let [sum (summaries/or-summary s @bound-atom)]
                  (println s sum @bound-atom) (Thread/sleep 100) 
                  (reset! bound-atom (summary/max-reward sum))
                  sum)))        
        sp-watch! (fn [sp]
                   (summaries/connect! sp ret true)
                   (connect-and-watch! ret sp
                     (fn [child-sp]
                       (let [child-ts (sp-ts child-sp)]
                         (summaries/connect! ret child-ts false)
                         (summaries/connect! child-ts ret true)
                         (summaries/summary-changed! ret)))))]
    (if-let [sp (get-stub-output stub)]
      (sp-watch! sp)
      (do (summaries/connect! stub ret true)
          (connect-and-watch! ret stub sp-watch!)))
    ret))

;; TODO: this basically looks just like old version now.
;; Main new idea was to be: auto-propagate subsumption arcs forward...
;; This is also what's needed for pess?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Stubs     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stub must implement Summarizable, optionally implements Evaluable

(defprotocol Stub
  (stub-name       [s])
  (input-set       [s])
  (tree-summarizer [s] "Summarizer that includes outputs/children."))

(defprotocol Evaluable (evaluate! [s]))

(defmethod print-method angelic.search.implicit.dash_astar.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Used by stubs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- with-subsuming-sp! [subsuming-sp stub]
  (when subsuming-sp
    (summaries/connect! (tree-summarizer stub) (sp-ts subsuming-sp) true))
  stub)

(defn- set-stub-output! [stub sp]
  (assert (empty? (get-outputs stub)))
  (summaries/summary-changed-local! stub)
  (add-output! stub sp))

(defn- get-stub-output  [s] (first (get-outputs s)))
(defn- get-stub-output! [s] (util/safe-singleton (get-outputs s)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Used on stubs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Just give output directly if subproblem is ready; return true if waiting
(defn- connect-and-watch-stub! [p c f]
  (assert (instance? angelic.search.implicit.dash_astar.Stub c))
  (if-let [sp (get-stub-output c)]
    (do (f sp) false)
    (do (summaries/connect! p c false)
        (add-watcher! c f)
        true)))

;; Used when p needs update if c does not produce immediate output.
(defn- connect-and-watch-stub-up! [p c f]
  (when (connect-and-watch-stub! p c f) (summaries/summary-changed! p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Making stubs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(traits/deftrait simple-stub [nm inp] [ts-atom (atom nil)] [watched-node]
  Stub
  (stub-name       [s] nm)
  (input-set       [s] inp)
  (tree-summarizer [s] (or @ts-atom (reset! ts-atom (make-tree-summarizer s)))))

(defn- make-evaluated-stub [nm in-set sp-fn]
  (let [ret (traits/reify-traits [summaries/worst-summarizable (simple-stub nm in-set)])]
    (set-stub-output! ret (sp-fn ret))
    ret))

;; TODO: Connect ts to something ??
(defn- make-wrapping-stub [[nm in-set] inner-stub sp-fn]
  (let [ts  (tree-summarizer inner-stub)
        ret (traits/reify-traits [summaries/or-summarizable]
              Stub (stub-name       [s] nm)
                   (input-set       [s] in-set)
                   (tree-summarizer [s] ts))]
    (connect-and-watch-stub! ret inner-stub #(set-stub-output! ret (sp-fn ret %)))
    ret))


(defmulti get-stub (fn [nm inp subsuming-sp] (first nm)))

;; TODO: canonicalize in make-stub, for everyone ? 
;; TODO: do lookups via normalized sequences? 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (terminal?         [s] "Subproblem will not return any outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn- sp-name [s] (stub-name (stub s)))
(defn- sp-ts   [s] (tree-summarizer (stub s)))

(defmethod print-method angelic.search.implicit.dash_astar.Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (sp-name sp)) o))

(defn- add-sp-child! [sp child-sp]
  (assert (not (terminal? sp)))
  (summaries/summary-changed-local! sp)
  (add-output! sp child-sp))

(traits/deftrait simple-subproblem [stb out-set term? ri-fn] [] [watched-node]
  Subproblem (stub            [s] stb)
             (output-set      [s] out-set)
             (terminal?       [s] term?)
             (refine-input    [s ni] (ri-fn s ni)))

;; Note: summary-fn should take subsuming-bound into account.
(defn- make-simple-subproblem [stub out-set terminal? summary-fn ri-fn]
  (traits/reify-traits
   [(simple-subproblem
     stub out-set terminal? ;; Note ni may have different context.
     (fn [s ni]
       (if (= ni (input-set stub)) stub (with-subsuming-sp! s (ri-fn s ni)))))]
   summaries/Summarizable (summarize [s] (summary-fn s 0))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Wrappers     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;     Output Collection     ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn oc-name [inner-name] [:OC inner-name])

(declare make-output-collecting-subproblem)
(defn- make-output-collecting-stub [inner-stub]
  (assert (not (= (first (stub-name inner-stub)) :OC)))
  (assert (not (= (first (stub-name inner-stub)) :SA)))
  (make-wrapping-stub 
   [(oc-name (stub-name inner-stub)) (input-set inner-stub)]
   inner-stub make-output-collecting-subproblem))

(defn- =-state-sets [s1 s2]
  (util/assert-is (= (state/current-context s1) (state/current-context s2)) "%s" [s1 s2])
  (= s1 s2))

(defn- make-output-collecting-subproblem [stb inner-sp]
  (let [ret (traits/reify-traits 
             [summaries/or-summarizable
              (simple-subproblem stb (output-set inner-sp) false
                #(doto (if (= (input-set stb) %2) stb (refine-input inner-sp %2))
                   (-> stub-name first #{:SA :OC} assert)))])] ;Needed when SA off
    (connect-and-watch! ret inner-sp
      (fn child-watch [o]
        (if (=-state-sets (output-set inner-sp) (output-set o))
          (do (connect-and-watch! ret o child-watch)
              (summaries/summary-changed! ret))
          (if (#{:SA :OC} (first (sp-name o))) 
            (add-sp-child! ret o)
            (connect-and-watch-stub! ret (make-output-collecting-stub (stub o))
              #(add-sp-child! ret %)))))) ;; No update needed
    ret))

(comment
 (defmethod make-stub* :OC [[_ inner-name :as n] inp subsuming-sp]
            (assert (nil? subsuming-sp))
            (make-output-collecting-stub (make-stub* inner-name inp nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;     State Abstraction     ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sa-name [inner-name] [:SA inner-name])

(declare make-state-abstracted-subproblem)

(defn- make-eager-state-abstracted-stub [inner-stub in-set]
  (make-wrapping-stub
   [(sa-name (stub-name inner-stub)) in-set]
   inner-stub make-state-abstracted-subproblem))


(defn- make-deliberate-state-abstracted-stub [inner-stub in-set]
  (if-let [out (get-stub-output inner-stub)]
    (let [done? (atom false)  
          ret
          (traits/reify-traits
           [(simple-stub [:SA (stub-name inner-stub) in-set] in-set)]
           summaries/Summarizable
           (summarize [s]
            (if @done? summary/+worst-simple-summary+
                (summary/make-live-simple-summary
                 (summary/max-reward (summaries/summary (sp-ts out))) s)))   
           Evaluable
           (evaluate! [s] (reset! done? true)
            (set-stub-output! s (make-state-abstracted-subproblem s out))))]
      (summaries/connect! ret out false)
      ret)
    (make-eager-state-abstracted-stub inner-stub in-set)))


(defn- make-state-abstracted-stub [inner-stub in-set]
  ((case *state-abstraction*
     :eager make-eager-state-abstracted-stub
     :deliberate make-deliberate-state-abstracted-stub)
   inner-stub in-set))


;; Note: subsumed subproblems can have different irrelevant vars
(defn- make-state-abstracted-subproblem [stb inner-sp]
  (let [in  (input-set stb)
        out (state/transfer-effects in (output-set inner-sp))
        ri-fn #(if (=-state-sets %2 in) stb (refine-input inner-sp %2))
        ret (traits/reify-traits
             [summaries/or-summarizable (simple-subproblem stb out (terminal? inner-sp) ri-fn)])]
    (connect-and-watch! ret inner-sp
      (fn [o] (connect-and-watch-stub-up! ret (make-state-abstracted-stub (stub o) in) #(add-sp-child! ret %))))
    ret))

(comment
  (defmethod make-stub* :SA [[_ inner-name :as n] inp subsuming-sp]
    (assert (nil? subsuming-sp))
    (make-state-abstracted-stub (make-stub* inner-name inp nil) inp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Names       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn atomic-name [fs] [:Atomic fs])
(defn pair-name [l r] [:Pair l r])

(defn left-factor [s]
  (loop [s (next s) ret (first s)]
    (if s
      (recur (next s) (pair-name ret (first s)))
      ret)))

(defn right-factor [[f & r]]
  (if (seq r)
    (pair-name f (right-factor r))
    f))

(defn- make-fs-seq-name [fs-seq]
  (assert (seq fs-seq))
  ((if *left-recursive* left-factor right-factor)
   (map atomic-name fs-seq)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-fs-seq-stub get-atomic-stub)

(defn- make-atomic-subproblem [stb out-set reward status subsuming-sp]
  (let [inp-set  (input-set stb)
        ri-fn    (fn [s ri] (get-stub (stub-name stb) inp-set s))]
    (cond (not (= status :live))
          (make-simple-subproblem
           stb out-set true
           (fn [s b] (summary/make-simple-summary (min (summaries/subsuming-bound s) b reward) status s)) ri-fn)
          
          (and subsuming-sp (not (terminal? subsuming-sp))) 
          (let [ret (make-simple-subproblem stb subsuming-sp out-set false summaries/or-summary ri-fn)]
            (connect-and-watch! ret subsuming-sp
              (fn [sub-out]
                (connect-and-watch-stub-up! ret (refine-input sub-out inp-set) #(add-sp-child! ret %))))
            ret)
          
          :else 
          (let [ret (make-simple-subproblem stb out-set false summaries/or-summary ri-fn)]
            (doseq [child-name (map make-fs-seq-name (fs/child-seqs (second (stub-name stb)) inp-set))]
              (connect-and-watch-stub! ret (get-stub child-name inp-set nil)
                 #(add-sp-child! ret %)))
            ret))))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn make-atomic-stub [nm inp-set subsuming-sp]
  (let [state (atom :ready)]  ;; set to [out-set reward] after first eval, then :go after second.
    (traits/reify-traits [(simple-stub nm inp-set)]
      summaries/Summarizable
      (summarize [s]
       (cond (= :ready @state) (summary/make-live-simple-summary (summaries/subsuming-bound s) s)
             (= :go    @state) summary/+worst-simple-summary+
             :else             (summary/make-live-simple-summary
                                (min (summaries/subsuming-bound s) (second @state)) s)))   
      Evaluable
      (evaluate! [s]
        (assert (not (= :go @state)))
        (let [fs     (second nm)
              ready? (= :ready @state)]
          (if-let [[out-set reward :as op] (if ready? (fs/apply-opt fs inp-set) @state)]
            (let [status (if ready? (fs/status fs inp-set)   :live)]
              (if (or (not ready?) (not (= status :live)))
                (do (reset! state :go)
                    (->> (make-atomic-subproblem s out-set reward status subsuming-sp)
                         (set-stub-output! s)))
                (do (reset! state op) (summaries/summary-changed! s))))
            (do (reset! state :go) (summaries/summary-changed! s))))))))


;; (since it may already exist)!
;; Note: we must always wrap in S-A stub to get effects out of logger.
(defmethod get-stub :Atomic [[_ fs :as n] inp-set subsuming-sp]
  (let [full-name [n (if *state-abstraction* (fs/extract-context fs inp-set) inp-set)]
        make-stub #(let [r (make-atomic-stub n % subsuming-sp)]
                     (if *collect-equal-outputs* (make-output-collecting-stub r) r))]
     (if-let [^HashMap dc *decompose-cache*]
       (if *state-abstraction*
         (let [stub (util/cache-with dc full-name (make-stub (fs/get-logger fs inp-set)))]
           (make-state-abstracted-stub stub inp-set))   
         (util/cache-with dc full-name (make-stub inp-set)))
       (make-stub inp-set))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)

;; Note: this is the only place logic depends on summary.  Potential for problems?
(defn- make-pair-subproblem [stb left-sp right-sp]
  (let [nm (stub-name stb)
        expand-right? (and (summary/solved? (summaries/summary left-sp)) (empty? (get-outputs left-sp)))
        kids (if expand-right? [(sp-ts left-sp) right-sp] [left-sp (sp-ts right-sp)])
        ss   (summaries/make-sum-summarizer kids)
        ret (make-simple-subproblem
             stb (output-set right-sp) false             
             (if (or expand-right? (not *collect-equal-outputs*)) summaries/or-summary
                 (let [left-done? (atom false)] ;; Manually take into account left-solved, when no output message.
                   (fn [s b] 
                     (when (and (not @left-done?) (summary/solved? (summaries/summary left-sp))) 
                       (reset! left-done? true) 
                       (summaries/disconnect! s ss)
                        ;; Make sure we don't double count, because child will use tree-summarizer of left.
                       (add-watcher! left-sp (fn [o] (def *sum* [s left-sp o])
                                               (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch-stub! s (make-pair-stub2 nm left-sp (stub right-sp))
                          (fn [os] (connect-and-watch! s os #(add-sp-child! s %))))) ;; no update needed 
                     (summaries/or-summary s b))))             
             (fn [s ri] (make-pair-stub1 nm (refine-input left-sp ri) #(refine-input right-sp %))))]
    (summaries/connect! ret ss false)
    (let [[watch stub-f] (if expand-right?
                           [right-sp #(make-pair-stub2 nm left-sp (stub %))]
                           [left-sp #(make-pair-stub2 nm % (refine-input right-sp (output-set %)))])]
      (add-watcher! watch
         (fn [o]
           (summaries/summary-changed-local! ss)
           (connect-and-watch-stub-up! ret (stub-f o) #(add-sp-child! ret %)))))
    ret))


(defn- make-pair-stub2 [nm left-sp right-stub]
  (let [is (input-set (stub left-sp))]
    (if-let [right-sp (get-stub-output right-stub)] ;; short-circuit the mess below
      (make-evaluated-stub nm is #(make-pair-subproblem % left-sp right-sp))
      (let [ret (traits/reify-traits [summaries/sum-summarizable (simple-stub nm is)])]
        (summaries/connect! ret (sp-ts left-sp) false)
        (connect-and-watch-stub! ret right-stub 
          #(set-stub-output! ret (make-pair-subproblem ret left-sp %)))
        ret))))

;; Note, potential to learn about additioan lsubsumption here, however, must be taken into account.
(defn- make-pair-stub1 [nm left-stub right-stub-fn]
  (if-let [left-sp (get-stub-output left-stub)]
    (make-pair-stub2 nm left-sp (right-stub-fn (output-set left-sp)))
    (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub nm (input-set left-stub))])]
      (connect-and-watch-stub! ret left-stub 
        (fn [lo]
          (connect-and-watch-stub-up! ret
            (make-pair-stub2 nm lo (right-stub-fn (output-set lo)))
            #(set-stub-output! ret %))))
      ret)))

(defmethod get-stub :Pair [[_ left-name right-name :as n] inp subsuming-sp]
  (assert (nil? subsuming-sp))
  (make-pair-stub1 n (get-stub left-name inp nil) #(get-stub right-name % nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- get-root-summarizer [inp-set fs]
  (tree-summarizer (make-atomic-stub (atomic-name fs) inp-set nil)))

(def *lazy-cache* false) 
(def *no-subsumption* false)
(def *assume-consistency* false) ;; Don't propagate lazy increases.

;; TODO: sa options...
(defn implicit-dash-a*
  [henv & {gather :gather d :d   s :s    choice-fn :choice-fn local? :local?  dir :dir :as m
      :or {gather true   d true s :eager choice-fn last       local? true     dir :right}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir} (keys m)))
  (assert (contains? #{:left :right} dir))
  (assert (contains? #{nil false :eager :deliberate} s))
  (when s (assert d))
  (when d (assert gather))
;  (assert (contains? #{:uncached :lazy :eager  :eager-nosub :eager-nokids} c))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (= dir :left)
 ;            summaries/*cache-method* c
            ]
    (summaries/solve
     (apply get-root-summarizer (fs/make-init-pair henv))
     choice-fn local? evaluate!
     #(let [n (second (sp-name %))] (when-not (= (first n) :noop) n)))))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (do (def s summaries/summarize) (def sc summary/children) (def nc summaries/node-ordinary-children) (def src summary/source))
;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) )))




