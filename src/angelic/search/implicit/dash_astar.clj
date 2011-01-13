(ns angelic.search.implicit.dash-astar
  (:require [edu.berkeley.ai.util :as util]
            [edu.berkeley.ai.util.traits :as traits]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summaries :as summaries]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

;; A revampting of dash_astar_opt, to move subsumption relationships and caching
;; out into a separate class.  This is necessary to keep pessimistic and optimistic
;; things in sync, and should help simplify and generalize subsumption stuff.

;; Here we replace all subsumption with consistency-maintaining and TDBs in summaries.
;; This simplifies problems with cycles that arrise when doing subsumption right.

;; All TODOs from dash_astar_opt also apply here.

;; TODO: SP has hash table from (state-abstracted context) input set to stub (?).
;; TODO: How are subsumption links handled?  

;; TODO: add pess

;; TODO: we need to make sure tree sums get called on add-output! first to ensure
;;       consistency with top-down-bounds ? 

;;  (except ensuring consistency if we're asserting it...)
;; When we create a stub, we also get: tree summarizer, subsumption-thing.
;; TODO: tests ! 

;; What do we do about multiple ways to express a given plan ? ? ? ?
;; Can normalize or not, interesting question... start without. 

;; TODO: remove refs to stubs in TS so dead weight can be GC'd?
;; TODO first: propagate subsumption links.
;; TODO second: add pessimistic variant. (primitives shared!)

;; TODO: bounding of pessimistic descriptions ? (assume consistency for now).

;; Two basic kinds of subsumption propagation:
;;   X --> Y ==> for all child keys k, child(X, k) --> child(Y, k)
;;   This taken into account for atomic, not pairs now.

;;   X --> Y ==> for all child keys k, child(X, k) --> child(Y, k)

;; --> TODO: every SP should watch all subsuming SPs for children with matching
;;     names, add these as subsumption parents.
;; (Except any direct parents)
;; --> TODO: this should happen as soon as stub is created, not have to wait for SP.
;; This means that TS needs to know about stubs-in-training.

;; TODO: wrapping names don't match pair-stub1.  Get rid of norm-name hack?
;; TODO: subsumptin should be sets, not lists? 



(set! *warn-on-reflection* true)

(def *left-recursive*        true) ;; Use left, not right recursion for seqs (((a . b) . c) . d) 
(def *collect-equal-outputs* true) ;; Collect identical output sets
(def *decompose-cache*       true) ;; nil for none, or bind to hashmap
(def *state-abstraction*     :eager ) ;; Or lazy or nil.
(def *propagate-subusmption* false)


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
    (.add outputs o) (assert (not (= sw o)))
    (doseq [w (doall (seq watchers))] (swap! *out-count* inc) (w o)))
  (get-outputs [sw] (doall (seq outputs))))

(defn- connect-and-watch! [p c f]
  (summaries/connect! p c)
  (add-watcher! c f))

;;;;;;;;;;;;;;;;;;;;;;;;;;      Tree Summarizers      ;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare sp-ts get-stub-output norm-name)

;; TODO: now this will never be true; how to avoid extra connections ?
(defprotocol TreeSummarizer
  (ts-stub [ts])
  (subsuming-sps [ts]) ; True tree summarizers subsuming this one.
  (add-subsuming-sp! [ts subsuming-sp]))  
  

(defn- make-tree-summarizer [stb]
  (let [subsuming-sp-set (IdentityHashMap.)
        ret (traits/reify-traits [summaries/or-summarizable summaries/simple-cached-node]
              TreeSummarizer
              (ts-stub [ts] stb)
              (subsuming-sps [ts] (keys subsuming-sp-set))
              (add-subsuming-sp! [ts subsuming-sp]
                (util/assert-is (= (norm-name (stub-name stb)) (norm-name (sp-name subsuming-sp))))                 
                (when-not (.containsKey subsuming-sp-set subsuming-sp)
                  (.put subsuming-sp-set subsuming-sp true)
                  (summaries/connect-subsumed! (sp-ts subsuming-sp) ts))))]
    (when-not (get-stub-output stb)
      (summaries/connect! ret stb)
      (summaries/connect-subsumed! ret stb))
    ret))

(defn tree-summarizer? [x] (instance? angelic.search.implicit.dash_astar.TreeSummarizer x))

(defmethod print-method angelic.search.implicit.dash_astar.TreeSummarizer [s o]
 (let [s (ts-stub s)]
  (print-method (format "#<TS$%8h %s>" (System/identityHashCode s) (stub-name s)) o)))

;; TODO: think about status of published output -- does it need updating ? 

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


;; TODO: set stub to -inf here, simplify other code? 
;; TODO: efficiency?
(defn- set-stub-output! [stb sp]
  (assert (empty? (get-outputs stb)))
  (assert (identical? (stub sp) stb)) 
  (let [b  (summaries/get-bound stb)
        ts (tree-summarizer stb)]
    (summaries/summary-changed-local! stb)    
    (summaries/connect-subsumed! ts sp)
    (connect-and-watch! ts sp
       (fn [child-sp]
         (let [child-ts (sp-ts child-sp)]
           (assert (tree-summarizer? child-ts))
           (summaries/connect! ts child-ts)
           (summaries/connect-subsumed! ts child-ts)
           (summaries/summary-changed! ts))))
;    (println "SO" stb b (summary/max-reward (summaries/summary sp)))
    (summaries/add-bound! ts b) ;; TODO: ???
    (summaries/summary-changed! ts)
    (add-output! stb sp)))

(defn- set-derived-stub-output! [stub sp]
  (assert (empty? (get-outputs stub)))
  (summaries/summary-changed-local! stub)    
  (add-output! stub sp))

(defn- get-stub-output  [s] (first (get-outputs s)))
(defn- get-stub-output! [s] (util/safe-singleton (get-outputs s)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Used on stubs ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Just give output directly if subproblem is ready; return true if waiting
;; if up?, updates p if c does not produce immediate output.
(defn- connect-and-watch-stub! [p c up? f]
  (assert (instance? angelic.search.implicit.dash_astar.Stub c))
  (if-let [sp (get-stub-output c)]
    (f sp)
    (do (summaries/connect! p c)
        (add-watcher! c f)
        (when up? (summaries/summary-changed! p)))))

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

(defn- make-wrapping-stub [[nm in-set] inner-stub sp-fn]
  (let [ret (traits/reify-traits [summaries/or-summarizable watched-node]
              Stub (stub-name       [s] nm)
                   (input-set       [s] in-set)
                   (tree-summarizer [s] (tree-summarizer inner-stub)))]
    (connect-and-watch-stub! ret inner-stub false #(set-derived-stub-output! ret (sp-fn ret %)))
    ret))


(defmulti get-stub (fn get-stub-dispatch [nm inp] (first nm)))

;; TODO: canonicalize in make-stub, for everyone ? 
;; TODO: do lookups via normalized sequences? 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: jsut incorporate Or into SP semantics?
(defprotocol Subproblem
  (stub              [s])
  (output-set        [s])
  (terminal?         [s] "Subproblem will not return any outputs.")
  (refine-input      [s refined-input-set] "Return a child stub."))

(defn- sp-name [s] (stub-name (stub s)))
(defn- sp-ts   [s] (tree-summarizer (stub s)))

(defmethod print-method angelic.search.implicit.dash_astar.Subproblem [sp o]
 (print-method (format "#<SP$%8h %s>" (System/identityHashCode (stub sp)) (sp-name sp)) o))

(defn direct-sp? [sp] )

(defn- add-sp-child-stub! [sp child-stub up?]
  (when (= (ts-stub (sp-ts sp)) (stub sp)) ;; not a wrapper; don't double-copy!
    ;; TODO
    )
  (connect-and-watch-stub! sp child-stub up?
    (fn [child-sp]
      (assert (not (terminal? sp)))
      (summaries/summary-changed-local! sp)
      (add-output! sp child-sp))))


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
       (if (= ni (input-set stub))
         stub
         (let [subsumed-stub (ri-fn s ni)]
           (add-subsuming-sp! (tree-summarizer subsumed-stub) s)
           subsumed-stub))))]
   summaries/Summarizable (summarize [s] (summary-fn s))))




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
          (let [c (if (#{:SA :OC} (first (sp-name o))) (stub o) (make-output-collecting-stub (stub o)))]
            (add-sp-child-stub! ret c false)))))
    ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;     State Abstraction     ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sa-name [inner-name] [:SA inner-name])

(declare make-state-abstracted-subproblem)

(defn- make-eager-state-abstracted-stub [inner-stub in-set]
  (make-wrapping-stub
   [(sa-name (stub-name inner-stub)) in-set]
   inner-stub make-state-abstracted-subproblem))

;; tODO: force ts? reward?
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
      (summaries/connect! ret out)
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
      (fn [o] (add-sp-child-stub! ret (make-state-abstracted-stub (stub o) in) true)))
    ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Names       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn atomic-name [fs] [:Atomic fs])
(defn pair-name [l r] [:Pair l r])

(defn left-factor [is]
  (loop [s (next is) ret (first is)]
    (if s (recur (next s) (pair-name ret (first s))) ret)))

(defn right-factor [[f & r]]
  (if (seq r) (pair-name f (right-factor r)) f))

(defn- make-fs-seq-name [fs-seq]
  (assert (seq fs-seq))
  ((if *left-recursive* left-factor right-factor)
   (map atomic-name fs-seq)))

;; TODO: flatten as well?
(defn norm-name [n]
  (case (first n)
    :Atomic n
    :Pair   [:Pair (norm-name (nth n 1)) (norm-name (nth n 2))]
    :SA     (norm-name (second n))
    :OC     (norm-name (second n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-fs-seq-stub get-atomic-stub)

;; TODO: we keep reward for :blocked case
;; Note: weirdly, sometimes ignoring it helps. (not always)
;; Three cases here: terminal, subsuming sp to piggyback, fresh.
(defn- make-atomic-subproblem [stb out-set reward status]
  (let [inp-set  (input-set stb)
        ri-fn    (fn [s ri] (get-stub (stub-name stb) ri))]
    (if (not (= status :live))
      (let [leaf-s #(summary/make-simple-summary (min (summaries/get-bound %) reward) status %)]
        (make-simple-subproblem stb out-set true leaf-s ri-fn))
      (let [ret (make-simple-subproblem stb out-set false summaries/or-summary ri-fn)]
        (if-let [subsuming-sps (seq (filter #(not (terminal? %)) (subsuming-sps (tree-summarizer stb))))]
          (connect-and-watch! ret (apply min-key (comp summary/max-reward summaries/summary sp-ts) subsuming-sps)
            (fn [sub-out]
              (add-sp-child-stub! ret (refine-input sub-out inp-set) true)))
          (doseq [child-name (map make-fs-seq-name (fs/child-seqs (second (stub-name stb)) inp-set))]
            (add-sp-child-stub! ret (get-stub child-name inp-set) false))) 
        ret))))

;; Note: this is double-stage to lazily generate children.  Could be simpler single-stage.
(defn make-atomic-stub [nm inp-set]
  (let [state (atom :ready)]  ;; set to [out-set reward] after first eval, then :go after second.
    (traits/reify-traits [(simple-stub nm inp-set)]
      summaries/Summarizable
      (summarize [s]
       (cond (= :ready @state) (summary/make-live-simple-summary (summaries/get-bound s) s)
             (= :go    @state) summary/+worst-simple-summary+
             :else             (summary/make-live-simple-summary
                                (min (summaries/get-bound s) (second @state)) s)))   
      Evaluable
      (evaluate! [s]
        (assert (not (= :go @state)))
        (let [fs     (second nm)
              ready? (= :ready @state)]
          (if-let [[out-set reward :as op] (if ready? (fs/apply-opt fs inp-set) @state)]
            (let [status (if ready? (fs/status fs inp-set)   :live)]
;              (println "eval" nm inp-set reward status)
              (if (or (not ready?) (not (= status :live)))
                (do (reset! state :go)
                    (->> (make-atomic-subproblem s out-set reward status)
                         (set-stub-output! s)))
                (do (reset! state op) (summaries/summary-changed! s))))
            (do (reset! state :go) (summaries/summary-changed! s))))))))


;; Note: we must always wrap in S-A stub to get effects out of logger.
(defmethod get-stub :Atomic [[_ fs :as n] inp-set]
  (let [full-name [n (if *state-abstraction* (fs/extract-context fs inp-set) inp-set)]
        make-stub #(let [r (make-atomic-stub n %)]
                     (if *collect-equal-outputs* (make-output-collecting-stub r) r))]
     (if-let [^HashMap dc *decompose-cache*]
       (if *state-abstraction*
         (let [stub (util/cache-with dc full-name (make-stub (fs/get-logger fs inp-set)))]
           (make-state-abstracted-stub stub inp-set))   
         (util/cache-with dc full-name (make-stub inp-set)))
       (make-stub inp-set))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Sequences    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare make-pair-stub1 make-pair-stub2)



(defn init-pair-sp! [sp r? l-sp r-sp]
  (let [ss (summaries/make-sum-summarizer (if r? [(sp-ts l-sp) r-sp] [l-sp (sp-ts r-sp)]))]
    (summaries/connect! sp ss)
    (let [[watch stub-f] (if r? [r-sp #(make-pair-stub2 l-sp (stub %))]
                                [l-sp #(make-pair-stub2 % (refine-input r-sp (output-set %)))])]
      (add-watcher! watch
        (fn [o]
          (summaries/summary-changed-local! ss)
          (add-sp-child-stub! sp (stub-f o) true))))))

;; Note: disconnect is needed since blocked trumps live.
;; TODO: get rid of disconnect -- just need to kill at the right time ?
;; Note: this is the only place logic depends on summary.  Potential for problems?
(defn- make-pair-subproblem [stb left-sp right-sp]
  (let [expand-right? (and (summary/solved? (summaries/summary left-sp)) (empty? (get-outputs left-sp)))
        ret (make-simple-subproblem
             stb (output-set right-sp) false             
             (if (or expand-right? (not *collect-equal-outputs*)) ;; Switch to right when left solved, no output.
               summaries/or-summary
               (let [left-done? (atom false)]
                 (fn [s] 
                   (when (and (not @left-done?) (summary/solved? (summaries/summary left-sp))
                              (empty? (get-outputs left-sp)))
                     (reset! left-done? true)
                     (summaries/disconnect! s (util/safe-singleton (summaries/child-nodes s)))
                     (add-watcher! left-sp (fn [o] (throw (RuntimeException. "Solved and children."))))                     
                     (init-pair-sp! s true left-sp right-sp))       
                   (summaries/or-summary s))))             
             (fn [s ri] (make-pair-stub1 (stub-name stb) (refine-input left-sp ri) #(refine-input right-sp %))))]
    (init-pair-sp! ret expand-right? left-sp right-sp)
    ret))


(defn- make-pair-stub2 [left-sp right-stub]
;  (util/assert-is (= (first (sp-name left-sp)) :SA))
;  (util/assert-is (= (first (stub-name right-stub)) :SA))  
  (let [nm (pair-name (sp-name left-sp) (stub-name right-stub))
        is (input-set (stub left-sp))]
    (assert (= (output-set left-sp) (input-set right-stub)))
    (if-let [right-sp (get-stub-output right-stub)] ;; short-circuit the mess below
      (make-evaluated-stub nm is #(make-pair-subproblem % left-sp right-sp))
      (let [ret (traits/reify-traits [summaries/sum-summarizable (simple-stub nm is)])]
        (summaries/connect! ret (sp-ts left-sp))
        (connect-and-watch-stub! ret right-stub false
          #(set-stub-output! ret (make-pair-subproblem ret left-sp %)))
        ret))))


;; Note: this allows us to assert stub-sp matching.
;; TODO: get rido f this
(defn make-echo-subproblem [stb sp]
  (let [ret (make-simple-subproblem stb (output-set sp) (terminal? sp) summaries/or-summary
                                    (fn [s ri] (refine-input sp ri)))]
    (connect-and-watch! ret sp #(add-sp-child-stub! ret (stub %) false))
    ret))


;; TODO: remove extra level of indirection?
;; TODO: name does not match wrapping names.

(defn- make-pair-stub1 [nm left-stub right-stub-fn]
  (if-let [left-sp (get-stub-output left-stub)]
    (make-pair-stub2 left-sp (right-stub-fn (output-set left-sp)))
    (let [ret (traits/reify-traits [summaries/or-summarizable (simple-stub nm (input-set left-stub))])]
      (connect-and-watch-stub! ret left-stub false
        (fn [lo]
          (connect-and-watch-stub! ret
            (make-pair-stub2 lo (right-stub-fn (output-set lo)))
            true
            #(set-stub-output! ret (make-echo-subproblem ret %))))) ;; eek!
      ret)))

(defmethod get-stub :Pair [[_ left-name right-name :as n] inp]
  (make-pair-stub1 n (get-stub left-name inp) #(get-stub right-name %)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- get-root-summarizer [inp-set fs]
  (tree-summarizer (make-atomic-stub (atomic-name fs) inp-set )))

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
     #(let [n (fs/fs-name (second (sp-name %)))] (when-not (= (first n) :noop) n)))))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch 'angelic.search.implicit.fah-astar-expand 'angelic.search.implicit.fah-astar-eval 'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

;; (do (use '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.search.implicit.dash-astar 'angelic.domains.discrete-manipulation) (require '[angelic.search.explicit.hierarchical :as his]))

; (require '[angelic.search.implicit.dash-astar :as da] '[angelic.search.implicit.dash-astar-opt :as dao])

;;(do (defn s [x]  (summaries/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (summaries/child-nodes x)))

;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (time (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (println (run-counted #(second (implicit-dash-a* h))) @summaries/*summary-count*)))))


;; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env [5 3] [1 1] [ [ [2 2] [3 2] ] ] [ [:a [2 2] [ [3 2] [3 2] ] ] ] 1))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count*)) )))


;;(dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-hard-discrete-manipulation-env 2 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) (time (println (run-counted #(identity (his/explicit-simple-dash-a* h ))) @summaries/*summary-count* @*out-count*)) )))

; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! *out-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy (make-random-discrete-manipulation-env 4 3))]  (time (println (run-counted #(identity (implicit-dash-a* h))) @summaries/*summary-count* @*out-count*)) )))


; (dotimes [_ 1] (reset! summaries/*summary-count* 0) (reset! da/*out-count* 0) (reset! dao/*out-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 2 1 0) true)]  (time (println (run-counted #(identity (da/implicit-dash-a* h :gather false :d false :s nil))) @summaries/*summary-count* @da/*out-count*)) (time (println (run-counted #(identity (dao/implicit-dash-a*-opt h :gather false :d false :s nil))) @summaries/*summary-count*  @dao/*out-count*)) )))

