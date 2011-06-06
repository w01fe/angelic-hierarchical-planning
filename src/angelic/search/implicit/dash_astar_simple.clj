(ns angelic.search.implicit.dash-astar-simple
  (:require [angelic.util :as util]
	    [angelic.util.channel :as channel]
            [angelic.search.summary :as summary]            
            [angelic.search.summary-graphs-newer :as sg]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

(set! *warn-on-reflection* true)

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

;; TODO: TODO TODO TODO why refining of outer children in refine-input ? 

;; TODO: lots of expnad-pairs in dm.



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
  [config nm inp-set out-set wrapped-ts ri-fn summary-fn]
  (with-meta (assoc (sg/make-simple-cached-node)
               :config config
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
              (doto (with-meta (merge {:ts-sp sp
                                       :summarize-fn (util/safe-get (:config sp) :or-summarize)}
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

(defn make-output-collector [config nm inp-sets out-sets]
  (make-subproblem
   config
   [:OC nm #_ out-sets #_ (angelic.env.state/extract-context (second out-sets) (angelic.env.state/current-context (second out-sets)))] inp-sets out-sets nil 
   (fn ri-fn [oc ni]
     (if (fs/eq-sets = ni inp-sets)
       oc
       (refine-channel (:inner-child-channel oc) (make-output-collector config nm ni out-sets))))
   (util/safe-get config :or-summarize)))


(defn- publish-inner-child! [sp child-sp]
  (connect-and-watch! sp child-sp (partial publish-child! sp))
  (channel/publish! (:inner-child-channel sp) child-sp)
  (sg/status-increased! sp child-sp))

(defn publish-child! [sp child-sp]
  (when child-sp			
    (util/print-debug 2 "AC" sp child-sp)
    (util/assert-is (not (identical? sp child-sp)))
    (if (and (util/safe-get (:config sp) :collect?)
             (fs/eq-sets fs/=-state-sets (:output-sets sp) (:output-sets child-sp)))
      (publish-inner-child! sp child-sp)
      (do (when (canonical? sp)
            (sg/connect-subsumed! (sp-ts sp) (sp-ts child-sp))
            (sg/connect! (sp-ts sp) (sp-ts child-sp))
            (sg/status-increased! (sp-ts sp) (sp-ts child-sp)))
          (if (util/safe-get (:config sp) :collect?)
            (let [^HashMap com (:child-output-map sp)
                  [oc new?] (or (when-let [oc  (.get com (:output-sets child-sp))]
                                  [oc false])
                                (let [oc (make-output-collector
                                          (:config sp) (:name sp) (:input-sets sp) (:output-sets child-sp))]
                                  (.put com (:output-sets child-sp) oc)
                                  [oc true]))]
              (publish-inner-child! oc child-sp)
              (when new? (channel/publish! (:child-channel sp) oc)))              
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
    (when (util/safe-get (:config s) :propagate-subsumption?)
      (subscribe-children! s
        (fn [child]
          (let [can-child (canonicalize child)]
            (subscribe-children! subsuming-sp
              (fn [subsuming-child]
                (let [can-subsuming-child (canonicalize subsuming-child)]
                  (when (= (:name can-child) (:name can-subsuming-child))
                    (add-subsuming-sp! can-child can-subsuming-child))))))))))))


;; Note: used to verify =-state-sets on entry to sa
(defn refine-input    [s ni]
  (if (fs/eq-sets = (:input-sets s) ni)
    s
    (when-let [ret ((:refine-input-fn s) s ni)]
      (util/assert-is (= (:name s) (:name ret)))
      (when (canonical? s) (add-subsuming-sp! ret s))
      ret)))
  
(defn solved-terminal? [sp]
  (and (empty? (list-children sp))
       (summary/solved? (sg/summary sp))))


(defmethod print-method ::Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode sp) (:name sp)) o))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;           Names          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn atomic-name [fs] [:Atomic fs])

(defn atomic-name-fs [n] (assert (#{:Atomic} (first n))) (second n))

(defn pair-name [l r] [:Pair l r])

(defn sa-name [inner-name] [:SA inner-name])


(defn- left-factor [is]
  (loop [s (next is) ret (first is)]
    (if s (recur (next s) (pair-name ret (first s))) ret)))

(defn- right-factor [[f & r]]
  (if (seq r) (pair-name f (right-factor r)) f))

(defn- refinement-names
  "Generate the names of subproblems representing refinements of fs from inp-set,
   in canonical form."
  [config fs inp-sets]
  (for [fs-seq (fs/child-seqs fs (second inp-sets))]
    ((if (util/safe-get config :left-recursive?) left-factor right-factor)
     (map (if (util/safe-get config :abstract?)
            (comp sa-name atomic-name)
            atomic-name)
          fs-seq))))

(defmulti get-subproblem (fn get-sp-dispatch [config nm inp-sets] (first nm)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Atomic subproblems represent the plans for a single action from an input set.

;; Initially we are evaluated but have no children. (Lazy can be simulated by hierarchy)
;; Expanding generates and publishes child subproblems, based on children of subsuming if possible.



;; TODO: this assumes no inner child releases another inner child.  
;; Note: treatment of subsuming-sps was wrong in several ways ...
;; Right thing is: if not expandable, start fresh.
;; If expandable and expanded, do current thing (except, also wait on inner???)
;; If expandable and not expanded, do current thing
;; (problem is, inner bits may be hidden; may have non-correspondence).
;; TODO: all-child-channel!

(defmacro cache-under [dc ks body]
  `(if-let [^HashMap dc# ~dc]
     (util/cache-with dc# ~ks ~body)
     ~body))

(defn- make-atomic-subproblem [config fs inp-sets subsuming-sp]
  (let [nm (atomic-name fs)]
    (cache-under (util/safe-get config :decompose?)
                 [nm (if (util/safe-get config :abstract?)
                       (fs/map-sets fs/extract-context fs inp-sets)
                       inp-sets)]
     (let [[out-sets rewards status] (fs/apply-descs fs inp-sets)]
       (when out-sets
         (let [expanded?  (atom false)
               summary-fn (atom #((:make-summary config) rewards status %))]
           (assoc 
            (make-subproblem
             config nm inp-sets out-sets nil     
             (fn [s ri] (make-atomic-subproblem config fs ri (when (= status :live) s)))
             (fn summarize [s] (@summary-fn s)))
            :subsuming-sp subsuming-sp
            :expanded?-atom expanded?
            :expand!-fn
            (fn expand! [s]
              (util/print-debug 1 "expand" nm)
              (reset! expanded? true)
              (reset! summary-fn (util/safe-get config :or-summarize))
              (if (and subsuming-sp @(:expanded?-atom subsuming-sp)) ;; TODO: don't require expanded?
                (do (refine-channel (:child-channel subsuming-sp) s)
                    (refine-channel (:inner-child-channel subsuming-sp) s))
                (doseq [ref-name (refinement-names config fs inp-sets)] 
                  (publish-child! s (get-subproblem config ref-name inp-sets))))))))))))

(defmethod get-subproblem :Atomic [config [_ fs] inp-sets]
  (make-atomic-subproblem config fs inp-sets nil))          


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


(declare make-half-pair-subproblem)

(defn- make-pair-subproblem [config left-sp right-sp]
  (when right-sp
    (let [nm          (pair-name (:name left-sp) (:name right-sp))
	  right?-atom (atom false) ;; Expand on right            
          go-right! (fn [ss]
		      (reset! right?-atom true)                          
		      (sg/disconnect! ss (sp-ts right-sp))
		      (subscribe-children! left-sp (fn [c] (def *bad* [ss c]) (assert (not "S + C"))))
		      (connect-and-watch! ss right-sp
                        #(publish-child! (util/safe-singleton (sg/parent-nodes ss))
                                         (make-pair-subproblem config left-sp %))))
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
                                       ((:make-summary config) [summary/neg-inf r] :live ss))))
                              (sg/sum-summary ss)))
                        :expand!-fn
                        (fn expand! [ss] 
                          (util/print-debug 1 "expand-pair" nm)
                          (go-right! ss)))
	  ret (make-subproblem config nm (:input-sets left-sp) (:output-sets right-sp) nil 		 
		(fn ri-fn [s ni]
		  (refine-channel (:child-channel s)
                   (make-half-pair-subproblem config (refine-input left-sp ni) #(refine-input right-sp %))))
                (util/safe-get config :or-summarize))]    
      (sg/connect! ret ss) 
      (connect-ts! ss right-sp)
      (connect-and-watch! ss left-sp
	#(publish-child! ret (make-pair-subproblem config % (refine-input right-sp (:output-sets %)))))    
      ret)))

(defn make-half-pair-subproblem [config left-sp right-fn]
  (when left-sp (make-pair-subproblem config left-sp (right-fn (:output-sets left-sp)))))

(defmethod get-subproblem :Pair [config [_ left-name right-name :as n] inp-sets]
  (make-half-pair-subproblem
   config 
   (get-subproblem config left-name inp-sets)
   #(get-subproblem config right-name %)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    SA Wrapper     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; Note: subsumed subproblems can have different irrelevant vars
;; Also note: new input can have subset of variables of old. (=-state-sets does ntthis now).
(defn- make-state-abstracted-subproblem [config fs inner-sp inp-sets]
  (when inner-sp
    (let [ret (make-subproblem 
               config (sa-name (:name inner-sp))
               inp-sets (map #(when %2 (fs/transfer-effects %1 %2))
                             inp-sets (:output-sets inner-sp))
               (sp-ts inner-sp)
               (fn ri-fn [sp ni]
                 (if (fs/eq-sets fs/=-state-sets ni inp-sets) sp
                     (let [log-ni (fs/map-sets fs/get-logger fs ni)
                           ri     (refine-input inner-sp log-ni)]                      
                       (refine-channel (:child-channel sp)
                         (make-state-abstracted-subproblem config fs ri ni)))))
               (util/safe-get config :or-summarize))]      
      (connect-and-watch! ret inner-sp 
       #(publish-child! ret (make-state-abstracted-subproblem config fs % inp-sets)))
      ret)))


(defmethod get-subproblem :SA [config [_ inner-n :as n] inp-sets]
  (let [fs (atomic-name-fs inner-n)]
    (assert (second inp-sets))
    (make-state-abstracted-subproblem config fs
      (get-subproblem config inner-n (fs/map-sets fs/get-logger fs inp-sets))
      inp-sets)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)

(defn- expand! [s]  ((:expand!-fn s) s))

(defn extract-action [sp]
  (let [fs (second (:name sp)) n (fs/fs-name fs)]
    (when-not (= (first n) :noop) fs)))

(defn implicit-dash-a* [henv & {:as opts}] 
  (let [defaults {:collect?               true  ; Don't publish child subproblems with identical outputs?
                  :decompose?             true  ; Decomposition.  Requires :collect?
                  :abstract?              true  ; State Abstraction.  Requires :d
                  :choice-fn              last  ; Choose a child node to evaluate 
                  :search-strategy        :ao   ; :ldfs, :ao, :ao-global (enumerates whole soln subtree)
                  :left-recursive?        false ; Factor sequences into pairs using left recursion
                  :propagate-subsumption? true  ; propagate subsumption from parents to matching children?
                  :weight                 nil}   ; Weight for bw-summary, nil for simple-summary.
        config    (-> (merge defaults opts)
                      (update-in [:decompose?] #(when % (HashMap.)))
                      (into (if-let [w (:weight opts)]
                              {:or-summarize sg/or-summary-bws
                               :make-summary (fn [[p-r o-r] stat src]
                                               (summary/make-bw-summary
                                                w p-r (min (sg/get-bound src) o-r) stat src))}
                              {:or-summarize sg/or-summary
                               :make-summary (fn [[p-r o-r] stat src]
                                               (summary/make-simple-summary
                                                (min (sg/get-bound src) o-r) stat src))})))
        [init fs] (fs/make-init-pair henv)
        root      (sp-ts (make-atomic-subproblem config fs [(when (:weight opts) init) init] nil))]
    (let [ks (util/keyset defaults)] (doseq [k (keys opts)] (util/assert-is (ks k))))
    (when (:abstract? config)  (assert (:decompose? config)))
    (when (:decompose? config)  (assert (:collect? config)))
    (def *root* root)
    (case (:search-strategy config)
          :ldfs (do (sg/ldfs! root (:choice-fn config) Double/NEGATIVE_INFINITY expand!)
                    (summary/extract-solution-pair (sg/summary root) extract-action))
          (summary/solve
           #(sg/summary root)
           (sg/best-leaf-operator
            (:choice-fn config)
            (case (:search-strategy config) :ao true :al-global false)
            (fn [s] (expand! s) (sg/summaries-decreased! [s])))
           extract-action))))


;; (do (use 'angelic.util '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.domains.discrete-manipulation 'angelic.search.implicit.dash-astar-simple) (require '[angelic.search.summary-graphs-newer :as sg] '[angelic.search.summary :as summary]) (defn s [x]  (sg/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (sg/child-nodes x)))

;; (require '[angelic.search.implicit.dash-astar-opt :as dao])
;; (require '[angelic.search.implicit.dash-astar-simple :as das])

;; (do (use 'clojure.test) (use 'angelic.test.search.implicit.dash-astar-opt-simple) (run-tests 'angelic.test.search.implicit.dash-astar-opt-simple))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 4 0) true)]  (time (println (run-counted #(identity (implicit-dash-a* h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 1 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env-regions [4 4] [1 1] [ [ [2 2] [3 3] ] ] [ [:a [2 2] [ [3 3] [3 3 ] ] ] ] 1 2 2 1))]   (time (println (run-counted #(identity (implicit-dash-a* h :gather true :d true :s :eager :dir :right))) @sg/*summary-count*)))))




;; (dorun (map println (map (juxt s identity) (->> *root* nc first nc first nc first nc first nc (drop 3) first nc last nc first nc last nc first nc first nc first nc first nc first nc first nc first nc first nc first nc second nc first nc first nc first nc first nc first nc first nc first nc))))