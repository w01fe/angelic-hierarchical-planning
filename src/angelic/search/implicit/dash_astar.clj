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

(defn- get-stub-output  [s] (first (get-outputs s)))
(defn- get-stub-output! [s] (util/safe-singleton (get-outputs s)))


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

;; TODO: fix cycles by making subsumption updates only happen when strictly < reward.
;; TODO: what updates are needed here?
(defn- make-tree-summarizer [stub]
  (let [bound-atom (atom 0)
        ret (traits/reify-traits [summaries/simple-cached-node]
              summaries/Summarizable
              (summarize [s]
                (let [s (summaries/or-summary s @bound-atom)]
                  (reset! bound-atom (summary/max-reward s))
                  s)))        
        sp-watch! (fn [sp]
                   (summaries/connect! sp ret true)
                   (connect-and-watch! ret sp
                     (fn [child-sp]
                       (let [child-ts (tree-summarizer (stub child-sp))]
                         (summaries/connect! ts child-ts false)
                         (summaries/connect! child-ts ts true)
                         (summaries/summary-changed! ts)))))]
    (if-let [sp (get-stub-output stub)]
      (sp-watch! sp)
      (do (summaries/connect! stub ts true)
          (connect-and-watch! ts stub sp-watch!)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;     StubFactories     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: is there a distinction between SF and subsumption meeting place?
;; Latter can use, e.g., normalized sequences?
;; As-is, is there any need for SF at all ? 

(defprotocol StubFactory
  (sf-name [sf])
  (get-stub [sf inp-set subsuming-sp]))

(defn make-simple-stub-factory [nm make-stub]
  (let [] ;    h (HashMap.)
    (reify StubFactory
      (sf-name [sf] nm)
      (get-stub [sf inp-set subsuming-sp]
        (let [stub (make-stub sf inp-set subsuming-sp)]
          (when subsuming-sp (add-subsuming-sp! stub subsuming-sp))
          stub)))))
  
 ;;        (util/cache-with h inp-set (make-stub inp-set)))
 
(defmulti make-stub-factory (fn [nm] (first nm)))

(def *sf-cache* nil)

(defn get-stub-factory [nm]
  (util/cache-with ^HashMap *sf-cache* nm (make-stub-factory nm)))

(defn get-stub-by-name [nm is] (get-stub (get-stub-factory nm) is nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Stubs     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stub must implement Summarizable, optionally implements Evaluable

(defprotocol Stub
  (stub-factory    [s])
  (input-set       [s])
  (tree-summarizer [s] "Summarizer that includes outputs/children."))

(defprotocol Evaluable (evaluate! [s]))

(defn stub-name [s] (sf-name (stub-factory s)))

(traits/deftrait simple-stub [sf inp] [ts-atom (atom nil)] [watched-node]
  Stub
  (stub-factory    [s] sf)
  (input-set       [s] inp)
  (tree-summarizer [s] (or @ts-atom (reset! ts-atom (make-tree-summarizer s)))))

(defmethod print-method angelic.search.implicit.dash_astar.Stub [s o]
  (print-method (format "#<ST$%8h %s>" (System/identityHashCode s) (stub-name s)) o))

(defn- add-subsuming-sp! [stub subsuming-sp]
  (summaries/connect! (tree-summarizer stub) (tree-summarizer (stub subsuming-sp)) true))

(defn- set-stub-output! [stub sp]
  (assert (empty? (get-outputs stub)))
  (summaries/summary-changed-local! stub)
  (add-output! stub sp))


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

(defn- make-wrapping-stub [[sf in-set] inner-stub sp-fn]
  (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub sf in-set)])]
    (connect-and-watch-stub! ret inner-stub #(set-stub-output! ret (sp-fn ret %)))
    ret))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (terminal?         [s] "Subproblem will not return any outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn- sp-name [s] (stub-name (stub s)))
(defn- sp-sf [s] (stub-factory (stub s)))

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
   [(simple-subproblem stub out-set ts terminal? ;; Note ni may have different context.
                       (fn [s ni] (if (= ni (input-set stub)) stub (ri-fn s ni))))]
   summaries/Summarizable (summarize [s] (summary-fn s 0))))



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
        ri-fn    (fn [s ri] (get-stub (stub-factory stb) inp-set s))]
    (cond (not (= status :live))
          (make-simple-subproblem
           stb out-set true
           (fn [s b] (summary/make-simple-summary (min (subsuming-bound s) b reward) status s)) ri-fn)
          
          (and subsuming-sp (not (terminal? subsuming-sp))) 
          (let [ret (make-simple-subproblem stb subsuming-sp out-set false summaries/or-summary ri-fn)]
            (connect-and-watch! ret subsuming-sp
              (fn [sub-out]
                (connect-and-watch-stub-up! ret (refine-input sub-out inp-set) #(add-sp-child! ret %))))
            ret)
          
          :else ;; TODO
          (let [ret (make-simple-subproblem stb out-set false summaries/or-summary ri-fn)]
            (doseq [child-name (map make-fs-seq-name (fs/child-seqs function-set inp-set))]
              (connect-and-watch-stub! ret (get-stub-by-name child-name inp-set)
                 #(add-sp-child! ret %)))
            ret))))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn- make-atomic-stub [sf inp-set subsuming-sp]
  (let [state (atom :ready)]  ;; set to [out-set reward] after first eval, then :go after second.
    (traits/reify-traits [(simple-stub sf inp-set)]
      summaries/Summarizable
      (summarize [s]
       (cond (= :ready @state) (summary/make-live-simple-summary (summaries/subsuming-bound s) s)
             (= :go    @state) summary/+worst-simple-summary+
             :else             (summary/make-live-simple-summary
                                (min (summaries/subsuming-bound s) (second @state)) s)))   
      Evaluable
      (evaluate! [s]
        (assert (not (= :go @state)))
        (let [fs     (second (sf-name sf))
              ready? (= :ready @state)]
          (if-let [[out-set reward :as op] (if ready? (fs/apply-opt fs inp-set) @state)]
            (let [status (if ready? (fs/status fs inp-set)   :live)]
              (if (or (not ready?) (not (= status :live)))
                (do (reset! state :go)
                    (->> (make-atomic-subproblem s subsuming-sp out-set reward status)
                         (set-stub-output! s)))
                (do (reset! state op) (summaries/summary-changed! s))))
            (do (reset! state :go) (summaries/summary-changed! s))))))))

(defmethod make-stub-factory :Atomic [[_ fs :as n]]
  (make-simple-stub-factory n make-atomic-stub))

;; TODO: subsuming-sp should get connected to atomic-stub outside of make-atomic-stub
;; (since it may already exist)!
;; Note: we must always wrap in S-A stub to get effects out of logger.
(comment
 (defn- get-atomic-stub [subsuming-sp inp-set function-set]
   (let [full-name [:Atomic (fs/fs-name function-set)
                    (if *state-abstraction* (fs/extract-context function-set inp-set) inp-set)]
         make-stub #(let [r (make-atomic-stub [:Atomic (fs/fs-name function-set)] subsuming-sp % function-set)]
                      (if *collect-equal-outputs* (make-output-collecting-stub r) r))]
     (if-let [^HashMap dc *decompose-cache*]
       (if *state-abstraction*
         (let [stub (util/cache-with dc full-name (make-stub (fs/get-logger function-set inp-set)))]
           (make-state-abstracted-stub stub inp-set))   
         (util/cache-with dc full-name (make-stub inp-set)))
       (make-stub inp-set)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)

;; Note: this is the only place logic depends on summary.  Potential for problems?
(defn- make-pair-subproblem [sf left-sp right-sp]
  (let [expand-right? (and (summary/solved? (summaries/summary left-sp)) (empty? (get-outputs left-sp)))
        kids (if expand-right? [(tree-summarizer left-sp) right-sp] [left-sp (tree-summarizer right-sp)])
        ss   (summaries/make-sum-summarizer kids)
        ret (make-simple-subproblem
             pair-stub (output-set right-sp) false             
             (if (or expand-right? (not *collect-equal-outputs*)) summaries/or-summary
                 (let [left-done? (atom false)] ;; Manually take into account left-solved, when no output message.
                   (fn [s b] 
                     (when (and (not @left-done?) (summary/solved? (summaries/summary left-sp))) 
                       (reset! left-done? true) 
                       (summaries/disconnect! s ss)
                        ;; Make sure we don't double count, because child will use tree-summarizer of left.
                       (add-watcher! left-sp (fn [o] (def *sum* [s left-sp o])
                                               (throw (RuntimeException. "Solved and children."))))
                       (connect-and-watch-stub! s (make-pair-stub2 sf left-sp (stub right-sp))
                          (fn [os] (connect-and-watch! s os #(add-sp-child! s %))))) ;; no update needed 
                     (summaries/or-summary s b))))             
             (fn [s ri] (make-pair-stub1 s (refine-input left-sp ri)
                          (sp-name right-sp) #(refine-input right-sp %))))]
    (summaries/connect! ret ss false)
    (let [[watch stub-f] (if expand-right?
                           [right-sp #(make-pair-stub2 nil left-sp (stub %))]
                           [left-sp #(make-pair-stub2 nil % (refine-input right-sp (output-set %)))])]
      (add-watcher! watch
         (fn [o]
           (summaries/summary-changed-local! ss)
           (connect-and-watch-stub-up! ret (stub-f o) #(add-sp-child! ret %)))))
    ret))


(defn- make-pair-stub2 [sf left-sp right-stub]
  (let [is (input-set (stub left-sp))]
    (if (get-stub-output right-stub) ;; short-circuit the mess below
      (doto (make-wrapping-stub [sf is] right-stub #(make-pair-subproblem %1 left-sp %2))
        (-> get-stub-output assert)) ;; summary of wrapping stub would be wrong, otherwise...
      (let [ret (traits/reify-traits [summaries/sum-summarizable (simple-stub sf is)])]
        (summaries/connect! ret (tree-summarizer left-sp) false)
        (connect-and-watch-stub! ret right-stub 
            #(set-stub-output! ret (make-pair-subproblem ret left-sp %)))
        ret))))

;; Note, potential to learn about additioan lsubsumption here, however, must be taken into account.
(defn- make-pair-stub1 [sf left-stub right-stub-fn]
  (if-let [left-sp (get-stub-output left-stub)]
    (make-pair-stub2 sf left-sp (right-stub-fn (output-set left-sp)))
   (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub sf (input-set left-stub))])]
     (connect-and-watch-stub! ret left-stub 
       (fn [lo]
         (connect-and-watch-stub-up! ret
           (make-pair-stub2 sf lo (right-stub-fn (output-set lo)))
           #(set-stub-output! ret %))))
     ret)))

(defmethod make-stub-factory :Pair [[_ left-name right-name :as n]]
  (let [left-sf  (get-stub-factory left-name)
        right-sf (get-stub-factory right-name)]           
    (make-simple-stub-factory n 
      (fn [sf inp sub-sp]
        (make-pair-stub1 sf (get-stub left-sf inp) #(get-stub right-sf %))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- get-root-subproblem [inp-set fs]
  (let [root-stub (make-atomic-stub nil nil inp-set fs)]
    (dotimes [_ 2] (evaluate! root-stub))
    (get-stub-output! root-stub)))

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
  (binding [*sf-cache*              (HashMap.)
            *collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (= dir :left)
 ;            summaries/*cache-method* c
            ]
    (summaries/solve
     (tree-summarizer (apply get-root-subproblem (fs/make-init-pair henv)))
     choice-fn local? evaluate!
     #(let [n (second (sp-name %))] (when-not (= (first n) :noop) n)))))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (do (def s summaries/summarize) (def sc summary/children) (def nc summaries/node-ordinary-children) (def src summary/source))
;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) )))




