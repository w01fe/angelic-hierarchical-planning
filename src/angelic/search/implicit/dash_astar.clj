(ns angelic.search.implicit.dash-astar
  (:require [angelic.util :as util]
	    [angelic.util.channel :as channel]
            [angelic.env.state :as state]
            [angelic.search.summary :as summary]            
            [angelic.search.summary-graphs-newer :as sg]
            [angelic.search.function-sets :as fs])
  (:import [java.util HashMap ArrayList IdentityHashMap]))

(set! *warn-on-reflection* true)

;; TODO: before publish:
;;FIX refine-input for oc subproblem to solution in thesis

;; Note: back to scheduled status increases
;;  status-increased can call summary before we're done.
;;  This can give it stale summary.
;;  So, we batch them, and skip when parent has no summary yet.
;; (parent must get attached somewhere, that'll handle it.)

;; For now, just do single tree on (pess, opt) pairs. (or pure opt).
;; Ideally, would have separate opt & pess trees as well for caching.

;; Rationale for why we need this:
;; Suppose I have A, B.  Opt description of A has 3 branches of output.
;; Pess has single empty branch.  [-inf -inf] is valid description of this branch.
;;  i.e., doing things that way is effectively pessimistic about opt.

;; Can try to do this as: separate trees, plus "bridge" superstructure built on
;; top.  Or, as scaffolding which controls construction of lower trees.
;; Scaffolding seems preferable.

;; Also add hierarchical output collecting.
;; Solution to avoid huge syntactic/semantic mess of true hierarchical output
;; collection, and infinite loops of flat output collection:
;; start new OC after input refined.  Don't add to OC if > reward.

;; TODO: RI of child not connected to child of RI.

;; TODO: summary/+ should take order into account? !  live iff left live or left solved, right live, ..

;; We refine right iff the left set is a singleton-in-context, which guarantees it cannot
;; have any refinemetns.

;; We retain the solved/blocked distinction in name, although both are now understood to
;; mean solved iff init and final are singletons, otherwise who knows or cares.

;; We explicitly set summaries to keywords until nodes are ready, to catch bugs early.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Subproblems  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn extract-context [inp-sets context]
  (if context
   [(when (first inp-sets) (state/extract-context (first inp-sets) context))
    (state/extract-context (second inp-sets) context)]
   inp-sets))

(defn get-logger [inp-sets context]
  (if context
    [(when (first inp-sets) (state/get-logger (first inp-sets) context))
     (state/get-logger (second inp-sets) context)]
    inp-sets))

(defn transfer-effects [inp-sets out-sets context]
  (if context
    (map #(when %2 (state/transfer-effects %1 %2)) inp-sets out-sets)
    out-sets))

(defn equal-in-context? [ss1 ss2 context]
  (fs/eq-sets (if context
                (fn [s1 s2] (every? identity (map #(= (state/get-var s1 %) (state/get-var s2 %)) context)))
                =)
              ss1 ss2))


(defn- make-subproblem
  "Make a subproblem with the given name and input-set.  If this is a wrapping
   subproblem (e.g., output collector or state abstractor), pass tree summarizer
   of wrapped SP; otherwise, pass nil and a tree summarizer will be created.
   eval!-fn, ri-fn, and summary-fn specify how to evaluate, refine input, and summarize."
  [config nm context inp-set out-set ri-fn summary-fn]
  (with-meta (assoc (sg/make-simple-cached-node)
               :summary-atom (atom :NOT-READY)
               :config config
               :name nm
               :context context
               :input-sets inp-set
               :output-sets out-set
               :ts-atom (atom nil)
               :child-channel    (channel/make-channel)
               :constituent-channel (channel/make-channel)
               :subsuming-sp-set (IdentityHashMap.)
               :refine-input-fn ri-fn
               :summarize-fn summary-fn)    
    {:type ::Subproblem}))


(defn subscribe-children!  [s w] (channel/subscribe! (:child-channel s) w))

(defn- connect-and-watch! [p c child-f]
  (sg/connect! p c)
  (subscribe-children! c child-f))

(defn sp-ts [sp]
  (or @(:ts-atom sp)
      (reset!
       (:ts-atom sp)
       (let [ts (with-meta (assoc (sg/make-simple-cached-node)
                             :ts-sp sp
                             :summarize-fn (util/safe-get (:config sp) :or-summarize)
                             :summary-atom (atom :NOT-READY))
                  {:type ::TreeSummarizer})]
         (sg/connect-subsumed! ts sp)
         (connect-and-watch!
          ts sp
          (fn [pub-sp]
            (sg/connect-subsumed! ts (sp-ts pub-sp))
            (sg/connect! ts (sp-ts pub-sp))
            (swap! (-> sp :config :status-increases) conj [ts (sp-ts pub-sp)])))
         (reset! (:summary-atom ts) nil)
         ts))))



(defmethod print-method  ::TreeSummarizer [s o]
  (print-method (format "#<TS %s>" (print-str (:ts-sp s))) o))



(declare publish-child! refine-input)

(defn refine-constituents! [parent-sp refined-sp]
  (channel/subscribe!
   (:constituent-channel parent-sp)
   #(publish-child! refined-sp true (refine-input % (:input-sets refined-sp))))
  refined-sp)

;; TODO: This could potentially cause an infinite loop, which the thesis solution fixes.
;; but, the RIOC case never seems to happen, so we skip it for now.
(defn make-output-collector [config nm context inp-sets out-sets]
  (let [ref-map (HashMap.)]
    (assoc
     (make-subproblem
      config
      [(gensym "oc") nm] context inp-sets out-sets 
      (fn ri-fn [oc ni] (println "RIOC")    
        (util/cache-with ref-map ni (refine-constituents! oc (make-output-collector config nm context ni out-sets))))
      (util/safe-get config :or-summarize))
     :oc-ref-map ref-map
     :summary-atom (atom nil))))


(defn- publish-inner-child! [sp child-sp]
  (connect-and-watch! sp child-sp (partial publish-child! sp false))
  (swap! (-> sp :config :status-increases) conj [sp child-sp]))

;; TODO: no OC when we can prove we don't need it?
(defn publish-child! [sp constituent? child-sp]
  (when child-sp			
    (util/assert-is (not (identical? sp child-sp)))
    (util/assert-is (= (:context sp) (:context child-sp))) ;; TODO: assert same irrel.
    (when constituent? (channel/publish! (:constituent-channel sp) child-sp))
    (util/print-debug 2 "AC" sp child-sp)
    (if (and (util/safe-get (:config sp) :collect?)
             (fs/eq-sets = (:output-sets sp) (:output-sets child-sp)))
      (publish-inner-child! sp child-sp)
      (if (= :hierarchical (util/safe-get (:config sp) :collect?))
        (let [^HashMap com (:oc-map (:config sp))
              k         [(:name sp) (System/identityHashCode sp) (:output-sets child-sp)]
              [oc new?] (or (when-let [oc (.get com k)]
                              (when (and (empty? ^HashMap (:oc-ref-map oc)) ;; TODO: careful here
                                         (<= (summary/max-reward (sg/summary (sp-ts child-sp)))
                                             (summary/max-reward (sg/summary (sp-ts oc))))
                                         (<= (summary/max-reward (sg/summary child-sp))
                                             (summary/max-reward (sg/summary oc))))
                                [oc false]))
                            (let [oc (make-output-collector
                                      (:config sp) (:name sp) (:context sp) (:input-sets sp) (:output-sets child-sp))]
                              (.put com k oc)
                              [oc true]))]
          (util/print-debug 3 "TO-OC" new? sp child-sp (summary/max-reward (sg/summary (sp-ts child-sp)))
                            (when-not new? (summary/max-reward (sg/summary (sp-ts oc)))))
          (publish-inner-child! oc child-sp)
          (channel/publish! (:constituent-channel oc) child-sp)
          (when new? (channel/publish! (:child-channel sp) oc))) 
        (channel/publish! (:child-channel sp) child-sp)))))


(defn subsuming-sps        [s] (keys (:subsuming-sp-set s)))

(defn add-subsuming-sp! [s subsuming-sp]
  (util/assert-is (= (:name s) (:name subsuming-sp)))
  (let [^IdentityHashMap subsuming-sp-set (:subsuming-sp-set s)]
  (when-not (or (identical? s subsuming-sp)
                (.containsKey subsuming-sp-set subsuming-sp))
    (.put subsuming-sp-set subsuming-sp true)
    (sg/connect-subsumed! (sp-ts subsuming-sp) (sp-ts s))
    (when (util/safe-get (:config s) :propagate-subsumption?)
      (subscribe-children! s
        (fn [child]
          (subscribe-children! subsuming-sp
            (fn [subsuming-child]
              (when (= (:name child) (:name subsuming-child))
                (add-subsuming-sp! child subsuming-child))))))))))


;; Note: we used to verify =-state-sets on entry to sa
(defn refine-input    [s ni]
  (if (equal-in-context? (:input-sets s) ni (:context s))
    s
    (when-let [ret ((:refine-input-fn s) s (get-logger ni (:context s)))]
                                        ;      (println "RI" s (:input-sets s) ni (try (fs/=-in-context (second (:input-sets s)) (second ni)) (catch Exception e :e)))
      (util/assert-is (= (:name s) (:name ret)))
      (add-subsuming-sp! ret s)
      ret)))
  

(defmethod print-method ::Subproblem [sp o]
  (print-method (format "#<SP$%8h %s>" (System/identityHashCode sp) (:name sp)) o))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;     Core Subproblems     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;           Names          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn atomic-name [fs] [:Atomic fs])

(defn atomic-name-fs [n] (assert (#{:Atomic} (first n))) (second n))

(defn pair-name [l r] [:Pair l r])

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
     (map atomic-name fs-seq))))

(defmulti get-subproblem (fn get-sp-dispatch [config nm context inp-sets] (first nm)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      Atomic       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Atomic subproblems represent the plans for a single action from an input set.

;; Initially we are evaluated but have no children. (Lazy can be simulated by hierarchy)
;; Expanding generates and publishes child subproblems, based on children of subsuming if possible.

(defmacro cache-under [dc ks body]
  `(if-let [^HashMap dc# ~dc]
     (util/cache-with dc# ~ks ~body)
     ~body))



(defn- make-atomic-subproblem [config fs inp-sets subsuming-sp]
  (let [nm (atomic-name fs)
        context (when (util/safe-get config :abstract?)
                  (fs/precondition-context-set fs (second inp-sets)))]
    (cache-under (util/safe-get config :decompose?)
                 [nm (extract-context inp-sets context)]
     (let [inp-sets (get-logger inp-sets context)
           [out-sets rewards status] (fs/apply-descs fs inp-sets)]
       (when out-sets
         (let [expanded?  (atom false)
               summary-fn (atom #((:make-summary config) rewards status %))]
           (assoc 
            (make-subproblem
             config nm context inp-sets out-sets 
             (fn [s ri] (make-atomic-subproblem config fs ri (when (= status :live) s)))
             (fn summarize [s] (@summary-fn s)))
            :summary-atom (atom nil)
            :subsuming-sp subsuming-sp
            :expanded?-atom expanded?
            :expand!-fn
            (fn expand! [s]
              (util/print-debug 1 "expand" s (when subsuming-sp true)
                                (and subsuming-sp @(:expanded?-atom subsuming-sp)))
              (reset! expanded? true)
              (reset! summary-fn (util/safe-get config :or-summarize))
              (if (and subsuming-sp @(:expanded?-atom subsuming-sp)) ;; TODO: don't require expanded?
;                (do (refine-channel (:child-channel subsuming-sp) s))
                (refine-constituents! subsuming-sp s)
                (doseq [ref-name (refinement-names config fs inp-sets)] 
                  (publish-child! s true (get-subproblem config ref-name context inp-sets))))))))))))

(defmethod get-subproblem :Atomic [config [_ fs] context inp-sets]
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
;; left subproblem cannot have refined outputs,


(declare make-half-pair-subproblem)

(defn- make-pair-subproblem [config context inp-sets mid-sets left-sp right-sp]
  (when right-sp
    (let [nm (pair-name (:name left-sp) (:name right-sp))
	  ss (assoc (sg/make-simple-cached-node)
               :summary-atom (atom :NOT-READY)
               :summarize-fn sg/sum-summary)
          out-sets (transfer-effects mid-sets (:output-sets right-sp) context)
	  ret (make-subproblem config nm context inp-sets out-sets
		(fn ri-fn [s ni] ;; TODO:
                  (make-half-pair-subproblem config context ni (refine-input left-sp ni) #(refine-input right-sp %)))
                (util/safe-get config :or-summarize))]    

      (sg/connect! ret ss)

      #_(println "RIGHT:" (fs/unrefinable-set? (second (:output-sets left-sp)))
               left-sp right-sp (second (:output-sets left-sp)))
      (if (fs/unrefinable-set? (second (:output-sets left-sp)))
        (do (sg/connect! ss (sp-ts left-sp))
            (connect-and-watch! ss right-sp
              (fn [rc] (publish-child! ret false
                        (make-pair-subproblem config context inp-sets mid-sets left-sp rc)))))
        (do (connect-and-watch! ss left-sp
              (fn [lc] (publish-child! ret false
                        (make-half-pair-subproblem config context inp-sets lc
                                                  #(refine-input right-sp %)))))
            (sg/connect! ss (sp-ts right-sp))))
    
      (reset! (:summary-atom ret) nil)
      (reset! (:summary-atom ss) nil)      
      ret)))

(defn make-half-pair-subproblem [config context inp-sets left-sp right-fn]
  (when left-sp
    (let [mid-sets (transfer-effects inp-sets (:output-sets left-sp) context)]
     (make-pair-subproblem config context inp-sets mid-sets left-sp (right-fn mid-sets)))))

(defmethod get-subproblem :Pair [config [_ left-name right-name :as n] context inp-sets]
  (make-half-pair-subproblem 
   config context (get-logger inp-sets context)
   (get-subproblem config left-name context inp-sets)
   #(get-subproblem config right-name context %)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Planning ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare *root*)

(defn extract-action [sp]
  (let [fs (second (:name sp)) n (fs/fs-name fs)]
    (when-not (= (first n) :noop) fs)))

(defn implicit-dash-a* [henv & {:as opts}] 
  (let [defaults {:collect?               :flat ; Collect children with = output? nil, :flat, or :hierarchical
                  :decompose?             true  ; Decomposition.  Requires :collect?
                  :abstract?              true  ; State Abstraction.  Requires :d
                  :choice-fn              last  ; Choose a child node to evaluate 
                  :search-strategy        :ao   ; :ldfs, :ao, :ao-global (enumerates whole soln subtree)
                  :left-recursive?        false ; Factor sequences into pairs using left recursion
                  :propagate-subsumption? true  ; propagate subsumption from parents to matching children?
                  :weight                 nil}   ; Weight for bw-summary, nil for simple-summary.
        status-increases (atom nil)
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
                                                (min (sg/get-bound src) o-r) stat src))}))
                      (assoc :oc-map (HashMap.)
                             :status-increases status-increases))
        [init fs] (fs/make-init-pair henv)
        root      (sp-ts (make-atomic-subproblem config fs [(when (:weight opts) init) init] nil))
        expand!   #_(fn [s] ((:expand!-fn s) s))
                  (fn [s]
                    ((:expand!-fn s) s)
                   (util/print-debug 1.2 "\nSTARTING INCREASES")
                   (doseq [[p c] @status-increases]
                     (sg/status-increased! p c))
                   (reset! status-increases nil)
                   (util/print-debug 1.2 "\nSTARTING DECREASES"))]
    (let [ks (util/keyset defaults)] (doseq [k (keys opts)] (util/assert-is (ks k))))
    (when (:abstract? config)  (assert (:decompose? config)))
    (when (:decompose? config)  (assert (:collect? config)))
    (assert (contains? #{nil :flat :hierarchical} (:collect? config)))
    (def *root* root)
    (case (:search-strategy config)
          :ldfs (do (sg/ldfs! root (:choice-fn config) Double/NEGATIVE_INFINITY expand!)
                    (summary/extract-solution-pair (sg/summary root) extract-action))
          (summary/solve
           #(sg/summary root)
           (sg/best-leaf-operator
            (:choice-fn config)
            (case (:search-strategy config) :ao true :ao-global false)
            (fn [s]
              (expand! s)
              (sg/summaries-decreased! [s])))
           extract-action))))


;; (do (use 'angelic.util '[angelic env hierarchy] 'angelic.domains.nav-switch  'angelic.domains.discrete-manipulation 'angelic.search.implicit.dash-astar-simple) (require '[angelic.search.summary-graphs-newer :as sg] '[angelic.search.summary :as summary]) (defn s [x]  (sg/summarize x)) (defn sc [x] (summary/children x))  (defn src [x] (summary/source x)) (defn nc [x] (sg/child-nodes x)))

;; (require '[angelic.search.implicit.dash-astar-opt :as dao])
;; (require '[angelic.search.implicit.dash-astar-simple :as das])

;; (do (use 'clojure.test) (use 'angelic.test.search.implicit.dash-astar-opt-simple) (run-tests 'angelic.test.search.implicit.dash-astar-opt-simple))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-nav-switch-hierarchy (make-random-nav-switch-env 20 4 0) true)]  (time (println (run-counted #(identity (implicit-dash-a* h))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 0 (let [h (make-discrete-manipulation-hierarchy  (make-random-hard-discrete-manipulation-env 3 3))]   (time (println (run-counted #(identity (implicit-dash-a*-opt h))) @sg/*summary-count*)))))

;; (dotimes [_ 1] (reset! sg/*summary-count* 0) (debug 1 (let [h (make-discrete-manipulation-hierarchy  (make-discrete-manipulation-env-regions [4 4] [1 1] [ [ [2 2] [3 3] ] ] [ [:a [2 2] [ [3 3] [3 3 ] ] ] ] 1 2 2 1))]   (time (println (run-counted #(identity (implicit-dash-a* h))) @sg/*summary-count*)))))




;; (dorun (map println (map (juxt s identity) (->> *root* nc first nc first nc first nc first nc (drop 3) first nc last nc first nc last nc first nc first nc first nc first nc first nc first nc first nc first nc first nc second nc first nc first nc first nc first nc first nc first nc first nc))))