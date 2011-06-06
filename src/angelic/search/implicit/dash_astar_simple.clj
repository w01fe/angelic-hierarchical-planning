(ns angelic.search.implicit.dash-astar-simple
  (:require [angelic.util :as util]
	    [angelic.util.channel :as channel]
            [angelic.search.summary :as summary]            
            [angelic.search.summary-graphs-newer :as sg]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

;; Take dash_astar_opt_simple and add back complexities from
;; dash_astar.clj.

;; Do bounded suboptimal by propagating pessimistic into optimistic, versus
;; other way?  Issue was that ???

;; One issue is with propagation -- can't just take the min thing, need
;; to construct a composite summary.
;; But this doesn't rule out pess-side thing, since the same fn could be used
;; on either side.

;; Note: ignoring subsumption, communication only needs to happen at leaves.
;; Problem can just be with aliasing.
;; Suppose I have A, B.  Opt description of A has 3 branches of output.
;; Pess has single empty branch.  [-inf -inf] is valid description of this branch.
;;  i.e., doing things that way is effectively pessimistic about opt.

;; Going other way, spse we have single vacuous opt branch.
;; Suppose I have some vacuous pessimistic description.  I accumulate
;; all upper bounds there,

;; Right way to do it is: store the combined info in the opt-pess subsumption links.
;; Or, just make nodes opt-pess pairs.  But then, we lose out on caching.
;; Can just add caching on top -- but we may want separate opt-only tree still?
;; Actually, pretty clear we still want separate trees, so knowledge transfers to
;; new pess match with a given opt, for example.
;; So, we actually want to build three trees for now.

;; Are we guaranteed that every pess has an opt parent?  Even in presence
;; of ouptut collecting, etc. ?
;; Bridge means: exists some set of sequences that produce this opt, pess set pair.

;; Can try to do this as: separate trees, plus "bridge" superstructure built on
;; top.  Or, as scaffolding which controls construction of lower trees.
;; Scaffolding seems preferable.

;; There's this logic that goes with names that's independent of everything.
;; Drop SA
;; Atomic = leaf
;; Pair = sum of individuals.

;; Then there's refinement logic --
;; How to generate and propagate children.
;; If we have all children,

;; What if we think of this as just pair thing?  Conceptually, really simple.
;; If this is the "ontological" thing, construting other trees after the fact
;; should be easy .... . . . ..
;; Start with that, just for fun.  

;; NOTE: output collecting is not really good enough, since any change in
;; recursive hierarchy can trigger infinite loop.  Need hierarchical
;; collecting of some sort.

;; This really throws a wrengh in things, cause output things are no longer really
;; subproblems, shouldn't have tree summarizers (?), etc.
;; Well, why not?  


;; Doing things this way, have to stay optimistic!  I.e., always publish, then decrease
;; lcoally ...

;; Note issue with subsumption at atomic: wrapped thing can become blocked, and we're stuck.

;; Two obvious problems
;; 1.  Once blocked propagates, solved can't beat it.
;; 2.  Massive proliferation of subproblems with cycles -- probbly due to OC ??


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Options      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set! *warn-on-reflection* true)

;; These are all bound by the implicit-dash-a* main fn at the end of this file.
(declare *left-recursive*        ) ;; Use left, not right recursion for seqs 
(declare *collect-equal-outputs* ) ;; Collect descendants with identical output sets
(declare *decompose-cache*       ) ;; Cache subproblems? Requires *collect-equal-outputs*
(declare *state-abstraction*     ) ;; Use state abstraction?  Requires *decompose-cache*
(declare *propagate-subsumption* ) ;; Propagate subsumption links to corresponding children
(declare *weight*                ) ;; weighted A* weight.

(defmacro cache-under [ks body]
  `(if-let [^HashMap dc# *decompose-cache*]
     (util/cache-with dc# ~ks ~body)
     ~body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;       Utilities      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;      Change Scheduling      ;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Trying to keep cached summaries up-to-date while simultaneously modifying the
;; subproblem graph is quite difficult and potentially error-prone.
;; This code allows the set of root subproblems with changed summaries to be recorded
;; during evaluation and tree update, and then played back once the tree is fixed,
;; decoupling the processes of tree change and summary updates.

;; Only increase should ever be change of status. live->blocked or solved.
;; This can only happen starting at expanded atomic leaf.
;; It can happen automatically, with no explicit calls to summary.
;; Iff status is increased with identical cost, propagate it all the way up
;; until hit a +.
;; Otherwise, it's a decrease.
;; Increase never changes children.
;; by simply following active links as long as cost i

;; TODO: summary/+ should take order into account !  live iff left live or left solved, right live, ..

;; In fact, what does blocked even do for us ? ?  ??? ? ?? ? ?? ??
;; Just forces us to work on left sometimes, that's all.
;; It's not a real part of the summary.

(defn- expand! [s]  ((:expand!-fn s) s))
(defn- expand-and-update! [s]
  (expand! s)
  (sg/summaries-decreased! [s]))

(comment
  (def or-summary sg/or-summary #_ sg/or-summary-bws)

  ;; TODO: bound
  (defn make-summary [[p-rew o-rew] stat src]
    (let [b (sg/get-bound src)]
      (summary/make-simple-summary (min b o-rew) stat src)
      #_ (summary/make-bw-summary *weight* p-rew (min b o-rew) stat src))))

(def or-summary sg/or-summary-bws)

;; TODO: bound
(defn make-summary [[p-rew o-rew] stat src]
  (let [b (sg/get-bound src)]
    (summary/make-bw-summary *weight* p-rew (min b o-rew) stat src)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subproblem has keys :name :input-set :output-set  :expand! :refine-input-fn
;; and fns  publish-child! list-children subscribe-children!
;;  subsuming-sps add-subsuming-sp! sp-ts

(defn- make-subproblem
  "Make a subproblem with the given name and input-set.  If this is a wrapping
   subproblem (e.g., output collector or state abstractor), pass tree summarizer
   of wrapped SP; otherwise, pass nil and a tree summarizer will be created.
   eval!-fn, ri-fn, and summary-fn specify how to evaluate, refine input, and summarize."
  [nm inp-set out-set wrapped-ts ri-fn summary-fn]
  (with-meta (assoc (sg/make-simple-cached-node)
               :name nm
               :input-sets inp-set
               :output-sets out-set
               :ts-atom (atom wrapped-ts)
               :child-channel    (channel/make-channel)
               :inner-child-channel (channel/make-channel)
               :subsuming-sp-set (IdentityHashMap.)
               :child-output-map        (HashMap.)
               :refine-input-fn ri-fn
               :summarize-fn summary-fn)    
    {:type ::Subproblem}))

(defn sp-ts [sp]
  (or @(:ts-atom sp)
      (reset! (:ts-atom sp)
              (doto (with-meta (merge {:ts-sp sp :summarize-fn or-summary}
                                      (sg/make-simple-cached-node))
                      {:type ::TreeSummarizer})
                (sg/connect! sp)
                (sg/connect-subsumed! sp)))))

(defmethod print-method  ::TreeSummarizer [s o]
  (print-method (format "#<TS %s>" (print-str (:ts-sp s))) o))

;; Canonical SPs are Atomic and Pair; wrappers use TS of inner SP.
(defn- canonicalize [sp] (:ts-sp (sp-ts sp)))
(defn- canonical? [sp] (identical? sp (canonicalize sp)))




(defn list-children        [s] (channel/publications (:child-channel s)))

(defn subscribe-children!  [s w] (channel/subscribe! (:child-channel s) w))

(defn- connect-and-watch! [p c child-f]
  (sg/connect! p c)
  (subscribe-children! c child-f))

(defn- connect-ts! [p c]
  (sg/connect! p (sp-ts c)))

;; TODO: issue is a general one with summary propagation and loops
;; This was never really properly handled -- lazy was the way out.

;; TODO TODO: this solution is not correct in presence of bounding ...
;; Is there an easy way to fix it ? ??
;; OC should treat parent as a child.

(declare publish-child! refine-input)

(defn refine-channel [channel refined-sp]
  (channel/subscribe! channel #(publish-child! refined-sp (refine-input % (:input-sets refined-sp))))
  refined-sp)

;; TODO: put out-sets back?

(defn make-output-collector [nm inp-sets out-sets]
  (make-subproblem
   [:OC nm #_ out-sets #_ (angelic.env.state/extract-context (second out-sets) (angelic.env.state/current-context (second out-sets)))] inp-sets out-sets nil 
   (fn ri-fn [oc ni]
     (if (fs/eq-sets = ni inp-sets)
       oc
       (refine-channel (:inner-child-channel oc) (make-output-collector nm ni out-sets))))
   or-summary))

(defn publish-child! [sp child-sp]
  (when child-sp			
    (util/print-debug 2 "AC" sp child-sp)
    (util/assert-is (not (identical? sp child-sp)))
    (if (and *collect-equal-outputs*
             (fs/eq-sets fs/=-state-sets (:output-sets sp) (:output-sets child-sp)))
      (do (connect-and-watch! sp child-sp (partial publish-child! sp))
          (channel/publish! (:inner-child-channel sp) child-sp)
          (sg/status-increased! sp child-sp))
      (do (when (canonical? sp)
            (sg/connect-subsumed! (sp-ts sp) (sp-ts child-sp))
            (sg/connect! (sp-ts sp) (sp-ts child-sp))
            (sg/status-increased! (sp-ts sp) (sp-ts child-sp)))
          (if *collect-equal-outputs*
            (let [^HashMap com (:child-output-map sp)
                  [oc new?] (or (when-let [oc  (.get com (:output-sets child-sp))]
 ;                                 (println "catch!" sp oc child-sp)
                                  [oc false])
                                (let [oc (make-output-collector
                                          (:name sp) (:input-sets sp) (:output-sets child-sp))]
                                  (.put com (:output-sets child-sp) oc)
                                  [oc true]))]
              (connect-and-watch! oc child-sp (partial publish-child! oc))
              (channel/publish! (:inner-child-channel oc) child-sp)
              (sg/status-increased! oc child-sp)
              (when new?
                (channel/publish! (:child-channel sp) oc)))              
            (do (channel/publish! (:child-channel sp) child-sp)))))))
;; TODO: how to refine-input of output collector ??


(defn subsuming-sps        [s] (keys (:subsuming-sp-set s)))

(defn add-subsuming-sp! [s subsuming-sp]
  (util/assert-is (canonical? s))
  (util/assert-is (canonical? subsuming-sp))                     
  (util/assert-is (= (:name s) (:name subsuming-sp)))
  (let [^IdentityHashMap subsuming-sp-set (:subsuming-sp-set s)]
  (when-not (or (identical? s subsuming-sp)
                (.containsKey subsuming-sp-set subsuming-sp))
    (.put subsuming-sp-set subsuming-sp true)
    (sg/connect-subsumed! (sp-ts subsuming-sp) (sp-ts s))
    (when *propagate-subsumption*  ;; TODO: efficiency, etc.
      (subscribe-children! s
        (fn [child]
          (let [can-child (canonicalize child)]
            (subscribe-children! subsuming-sp
              (fn [subsuming-child]
                (let [can-subsuming-child (canonicalize subsuming-child)]
                  (when (= (:name can-child) (:name can-subsuming-child))
                    (add-subsuming-sp! can-child can-subsuming-child))))))))))))


(defn refine-input    [s ni]
  (when-let [ret ((:refine-input-fn s) s ni)]
    (util/assert-is (= (:name s) (:name ret)))
    (when (canonical? s) (add-subsuming-sp! ret s))
    ret))
  

(comment
  (defn- terminal? [sp]
    (and (empty? (list-children sp))
         (not (summary/live? (sg/summary sp))))))

(defn solved-terminal? [sp]
  (and (empty? (list-children sp))
       (summary/solved? (sg/summary sp))))



(defmethod print-method ::Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode sp) (:name sp)) o))

;; Multimethod to get a subproblem by name, or nil for dead.
(defmulti get-subproblem (fn get-subproblem-dispatch [nm inp-sets] (first nm)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Atomic subproblems represent the plans for a single action from an input set.

;; Initially we are evaluated but have no children. (Lazy can be simulated by hierarchy)
;; Expanding generates and publishes child subproblems, based on children of subsuming if possible.

(defn atomic-name [fs] [:Atomic fs])
(defn atomic-name-fs [n] (assert (#{:Atomic} (first n))) (second n))

(declare refinement-names)


(defn get-input-key [fs inp-sets]
  (if *state-abstraction* (fs/map-sets fs/extract-context fs inp-sets) inp-sets))

;; Note: treatment of subsuming-sps was wrong in several ways ...
;; Right thing is: if not expandable, start fresh.
;; If expandable and expanded, do current thing (except, also wait on inner???)
;; If expandable and not expanded, do current thing
;; (problem is, inner bits may be hidden; may have non-correspondence).
;; TODO: all-child-channel!
(defn- make-atomic-subproblem [fs inp-sets subsuming-sp]
  (let [nm (atomic-name fs)]
    (cache-under [nm (get-input-key fs inp-sets)]
     (let [[out-sets rewards status] (fs/apply-descs fs inp-sets)]
       (when out-sets
         (let [expanded?  (atom false)
               summary-fn (atom #(make-summary rewards status %))]
           (assoc 
            (make-subproblem
             nm inp-sets out-sets nil     
             (fn [s ri]  #_ (assert (not *collect-equal-outputs*))  
               (if (fs/eq-sets = ri inp-sets) s (make-atomic-subproblem fs ri (when (= status :live) s))))
             (fn summarize [s] (@summary-fn s)))
            :subsuming-sp subsuming-sp
            :expanded?-atom expanded?
            :expand!-fn
            (fn expand! [s]
              (util/print-debug 1 "expand" nm)
              (reset! expanded? true)
              (reset! summary-fn or-summary)
              (if (and subsuming-sp @(:expanded?-atom subsuming-sp)) ;; TODO: don't require expanded?
                (do (refine-channel (:child-channel subsuming-sp) s)
                    (refine-channel (:inner-child-channel subsuming-sp) s))
                (doseq [ref-name (refinement-names fs inp-sets)] 
                  (publish-child! s (get-subproblem ref-name inp-sets))))))))))))


;; TODO: handle state abstraction
;; TODO: should wrap pairs like this too?
(defmethod get-subproblem :Atomic [[_ fs] inp-sets]
  (make-atomic-subproblem fs inp-sets nil))          


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Pair      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pair subproblems represent sequntial composition of two subproblems.

;; Thus, we use the output of the left-sp as input for right-sp,
;; and output of right-sp as output of the pair.

;; The slightly tricky part is generating children.  Both left-sp and right-sp
;; may have childen, but to search systematically we branch on only one at a time.
;; This means that our summary should consist of the sum of summaries of
;;   - The subproblem whose children we branch on, and
;;   - The tree summarizer of the other subproblem.

;; For now, always attempt to branch on the left subproblem first, unless the
;; left subproblem is terminal (no children), in which case we branch right.
;; Unfortunately, we don't know when we start if the left will be terminal
;; (under *collect-equal-outputs*), so we assume it's not, then switch if,
;; at any point, it becomes terminal.
;; Unfortunately, the only place we can tell if it becomes terminal is while
;; computing the summary of this node.  But, at that point we don't want to
;; trigger any tree modifications, since when summary updates and tree modifications
;; get interleaved arbitrarily, it gets really hard to maintain correctness.
;; So, if right-sp already has children, we make the SP a leaf and wait for
;; it to be evaluated to switch; otherwise, we safely switch immediately.

(defn pair-name [l r] [:Pair l r])

(declare make-half-pair-subproblem)

(defn- make-pair-subproblem [left-sp right-sp]
  (when right-sp
    (let [nm          (pair-name (:name left-sp) (:name right-sp))
	  right?-atom (atom false) ;; Expand on right            
          go-right! (fn [ss]
		      (reset! right?-atom true)                          
		      (sg/disconnect! ss (sp-ts right-sp))
		      (subscribe-children! left-sp (fn [c] (def *bad* [ss c]) (assert (not "S + C"))))
		      (connect-and-watch! ss right-sp
                        #(publish-child! (util/safe-singleton (sg/parent-nodes ss))
                                         (make-pair-subproblem left-sp %))))
	  ss          (assoc (sg/make-simple-cached-node)
                        :summarize-fn
                        (fn [ss] 
                          (or (and (not @right?-atom)
                                   (solved-terminal? left-sp)
                                   (if (empty? (list-children right-sp)) 
                                     (do (go-right! ss) nil)
                                     (let [r (min (+ (summary/max-reward (sg/summary left-sp))
                                                     (summary/max-reward (sg/summary (sp-ts right-sp))))
                                                  (sg/get-bound ss))]
                                       (make-summary [summary/neg-inf r] :live ss))))
                              (sg/sum-summary ss)))
                        :expand!-fn
                        (fn expand! [ss] 
                          (util/print-debug 1 "expand-pair" nm)
                          (go-right! ss)))
	  ret (make-subproblem nm (:input-sets left-sp) (:output-sets right-sp) nil 		 
		(fn ri-fn [s ni]
		  (if (fs/eq-sets = ni (:input-sets left-sp)) s
		      (refine-channel (:child-channel s) (make-half-pair-subproblem (refine-input left-sp ni) #(refine-input right-sp %)))))
                or-summary)]    
      (sg/connect! ret ss) 
      (connect-ts! ss right-sp)
      (connect-and-watch! ss left-sp
	#(publish-child! ret (make-pair-subproblem % (refine-input right-sp (:output-sets %)))))    
      ret)))

(defn make-half-pair-subproblem [left-sp right-fn]
  (when left-sp (make-pair-subproblem left-sp (right-fn (:output-sets left-sp)))))

(defmethod get-subproblem :Pair [[_ left-name right-name :as n] inp-sets]
  (make-half-pair-subproblem
   (get-subproblem left-name inp-sets)
   #(get-subproblem right-name %)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    SA Wrapper     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn sa-name [inner-name] [:SA inner-name])

;; Note: subsumed subproblems can have different irrelevant vars
;; Also note: new input can have subset of variables of old. (=-state-sets does ntthis now).
(defn- make-state-abstracted-subproblem [fs inner-sp inp-sets]
  (when inner-sp
    (let [ret (make-subproblem 
               (sa-name (:name inner-sp))
               inp-sets (map #(when %2 (fs/transfer-effects %1 %2))
                             inp-sets (:output-sets inner-sp))
               (sp-ts inner-sp)
               (fn ri-fn [sp ni]
                 (if (fs/eq-sets fs/=-state-sets ni inp-sets) sp
                     (let [log-ni (fs/map-sets fs/get-logger fs ni)
                           ri     (refine-input inner-sp log-ni)]                      
                       (refine-channel (:child-channel sp) (make-state-abstracted-subproblem fs ri ni)))))
               or-summary)]      
      (connect-and-watch! ret inner-sp 
       #(publish-child! ret (make-state-abstracted-subproblem fs % inp-sets)))
      ret)))


(defmethod get-subproblem :SA [[_ inner-n :as n] inp-sets]
  (let [fs (atomic-name-fs inner-n)]
    (assert (second inp-sets))
    (make-state-abstracted-subproblem fs
      (get-subproblem inner-n (fs/map-sets fs/get-logger fs inp-sets))
      inp-sets)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Refinement Names     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- left-factor [is]
  (loop [s (next is) ret (first is)]
    (if s (recur (next s) (pair-name ret (first s))) ret)))

(defn- right-factor [[f & r]]
  (if (seq r) (pair-name f (right-factor r)) f))

(defn- wrapped-atomic-name [fs]
  (let [in  (atomic-name fs)]
    (if *state-abstraction* (sa-name in) in)))

(defn- refinement-names
  "Generate the names of subproblems representing refinements of fs from inp-set"
  [fs inp-sets]
  (for [fs-seq (fs/child-seqs fs (second inp-sets))]
    ((if *left-recursive* left-factor right-factor)
     (map wrapped-atomic-name fs-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)

(defn extract-action [sp]
  (let [fs (second (:name sp)) n (fs/fs-name fs)] (when-not (= (first n) :noop) fs)))

(defn implicit-dash-a*
  "Solve this hierarchical env using implicit DASH-A*, or variants thereupon.  Options are:
    :gather    Don't publish child subproblems with identical outputs?
    :d         Decomposition: cache and re-use subproblems by [name inp-set] pair?  Requires :gather.
    :s         State Abstraction: take state abstraction into account when caching?  Requires :d.
    :choice-fn Choose a child node to evaluate from alternatives (in sequence)
    :local?    Apply choice-fn recursively at each pair, or to an entire leaf sequence (slower)?
    :dir       Factor sequences into pairs using :left or :right recursion
    :prop      Automatically propagate subsumption from parents to matching children?"
  [henv & {gather :gather d :d  s :s   choice-fn :choice-fn
           local? :local?  dir :dir   prop :prop strategy :strategy :as m
      :or {gather true   d true s true choice-fn last
           local? true     dir :right prop true strategy :ao}}]
  (assert (every? #{:gather :d :s :choice-fn :local? :dir :prop :strategy} (keys m)))
  (when s (assert d))
  (when d (assert gather))
  (binding [*collect-equal-outputs* gather
            *decompose-cache*       (when d (HashMap.))
            *state-abstraction*     s
            *left-recursive*        (case dir :left true :right false)
            *propagate-subsumption* prop
            *weight*                1.5]
    (let [[init fs] (fs/make-init-pair henv)] 
      (def *root* (sp-ts (make-atomic-subproblem fs [init init] nil))))
    (case strategy
          :ao (summary/solve
               #(sg/summary *root*)
               (sg/best-leaf-operator choice-fn local? expand-and-update!)
               extract-action)
          :ldfs (do (sg/ldfs! *root* choice-fn Double/NEGATIVE_INFINITY expand!)
                    (summary/extract-solution-pair (sg/summary *root*) extract-action)))))



;; (do (use 'angelic.util '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.domains.discrete-manipulation 'angelic.search.implicit.dash-astar-simple) (require '[angelic.search.summary-graphs-newer :as sg] '[angelic.search.summary :as summary]) (defn s [x]  (sg/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (sg/child-nodes x)))

;; (require '[angelic.search.implicit.dash-astar-opt :as dao])
;; (require '[angelic.search.implicit.dash-astar-simple :as das])

;; (do (use 'clojure.test) (use 'angelic.test.search.implicit.dash-astar-opt-simple) (run-tests 'angelic.test.search.implicit.dash-astar-opt-simple))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 4 0) true)]  (time (println (run-counted #(identity (implicit-dash-a* h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 1 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env-regions [4 4] [1 1] [ [ [2 2] [3 3] ] ] [ [:a [2 2] [ [3 3] [3 3 ] ] ] ] 1 2 2 1))]   (time (println (run-counted #(identity (implicit-dash-a* h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))




;; (dorun (map println (map (juxt s identity) (->> *root* nc first nc first nc first nc first nc (drop 3) first nc last nc first nc last nc first nc first nc first nc first nc first nc first nc first nc first nc first nc second nc first nc first nc first nc first nc first nc first nc first nc))))