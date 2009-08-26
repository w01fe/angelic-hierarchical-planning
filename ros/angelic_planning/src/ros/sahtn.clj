;///////////////////////////////////////////////////////////////////////////////
;// Robot state for high-level planning.
;//
;// Copyright (C) 2009, Jason Wolfe
;//
;// Redistribution and use in source and binary forms, with or without
;// modification, are permitted provided that the following conditions are met:
;//   * Redistributions of source code must retain the above copyright notice,
;//     this list of conditions and the following disclaimer.
;//   * Redistributions in binary form must reproduce the above copyright
;//     notice, this list of conditions and the following disclaimer in the
;//     documentation and/or other materials provided with the distribution.
;//   * Neither the name of Stanford University nor the names of its
;//     contributors may be used to endorse or promote products derived from
;//     this software without specific prior written permission.
;//
;// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
;// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;// POSSIBILITY OF SUCH DAMAGE.
;//////////////////////////////////////////////////////////////////////////////



(ns ros.sahtn
  (:import [java.util HashMap Random])
  (:use ros.ros [ros.robot-actions :as ra])
  )
  
(set! *warn-on-reflection* true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- map-keys [f m] (into {} (for [[k v] m] [(f k) v])))
(defn- map-vals [f m] (into {} (for [[k v] m] [k (f v)])))

(defn- merge-valuations [& vs]
  "Like merge-with max, but preserves metadata of the best key."
  (reduce 
   (fn [v1 v2] 
     (reduce 
      (fn [v1 [k v]]
	(if (<= v (get v1 k Double/NEGATIVE_INFINITY))
	    v1
	  (assoc (dissoc v1 k) k v)))
      v1 v2))
   (or (first vs) {}) (rest vs)))

(defn- immediate-refinements [h a s]
  (println "Now refining" (ra/robot-action-name a))
  (if (robot-hla-discrete-refinements? a)
      (ra/robot-hla-refinements (:nh h) a s)
    (let [num-refs (safe-get* (:sample-depths h) (:class a))
	  random   (Random. (+ (* 1000000 (:seed h)) (.hashCode #^Object a)))]
      (.nextDouble random) ;; First value from fresh random is distinctly not random.
      (filter identity
	(take num-refs
	  (repeatedly #(ra/sample-robot-hla-refinement-det (:nh h) a s random)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;; Computing result  valuations ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare sahtn-result)

(defn sahtn-compute-result-seq [h as v]
  "Compute result for sequence as for valuation v."
  (if (empty? as) v
    (recur h (rest as)
      (apply merge-with max
        (for [[s r] v]
	  (map-vals #(+ % r)
  	    (sahtn-result h (first as) s)))))))  

(defn sahtn-compute-result [h a s]
  "Actually refine a from state s.  Metadata on states gives best refinement to reach it."
  (let [{:keys [nh sample-depths]} h]
    (if (ra/robot-action-primitive? a)
        (apply hash-map (robot-primitive-result nh a s))
      (apply merge-valuations
	(for [ref (immediate-refinements h a s)]
	  (map-keys #(with-meta % {:ref ref})
	    (sahtn-compute-result-seq h ref {s 0})))))))

(defn sahtn-result [h a s]
  "Memoized result valuation for doing a from s."
  (let [#^HashMap cache (:cache h)
	context         (ra/robot-action-precondition-context a s)
	cache-key       [a context]
	cache-val       (.get cache cache-key)]
    (cond (nil? cache-val)           ;; Not computed, actually do work + cache result 
	    (do (.put cache cache-key :in-progress)
		(let [result        (sahtn-compute-result h a s)
		      effect-schema (ra/robot-action-effect-context-schema a)]		  
		  (.put cache cache-key 
		    (map-keys #(with-meta (cherry-pick effect-schema %) (meta %)) result))
		  result))
	  (= cache-val :in-progress) ;; On the stack; this is a loop.
	    {}
	  :else                      ;; already computed; reuse 
	    (do (println "Yippee! Reusing results for action" (ra/robot-action-name a))
		(map-keys #(merge-deep s %) cache-val)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Extracting Solutions  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add assertions

(declare sahtn-solution)

(defn sahtn-solution-seq [h as v final-s]
  "Returns [solution init-s init-rew].  Should always succeed."
;  (println (count as) (when (seq as) (ra/robot-action-name (first as))) (keys final-s)  (count v))
  (if (empty? as) 
      (do ;(println (:robot final-s) "\n\n\n" (map-keys :robot v) final-r (get v final-s))
	  (contains? v final-s)
	  [[] final-s])
    (let [a      (first as)
	  next-v (apply merge-valuations
		   (for [[s r]   v]
		     (into {}
		       (for [[ns sr] (sahtn-result h a s)]
			 [(with-meta ns {:pre s}) (+ r sr)]))))
	  [rest-sol step-final-s] (sahtn-solution-seq h (rest as) next-v final-s)
	  [my-fs my-fr]           (find next-v step-final-s)
	  my-is                   (:pre (meta my-fs))]
;      (println (count as))
;      (assert my-fs)
;      (assert my-is)
;      (println step-final-r my-fr)
      (assert (= my-fs step-final-s)) ; (= my-fr step-final-r)))
      [(concat (sahtn-solution h a my-is my-fs) rest-sol)
       my-is])))

(defn sahtn-solution [h a s final-s]
  "Returns a solution (possibly [])."
  (println "Extracting solution for" (ra/robot-action-name a))
  (let [#^HashMap cache   (:cache h)
	context           (ra/robot-action-precondition-context a s)
	cache-key         [a context]
	cache-val         (.get cache cache-key)
	final-s-context   (cherry-pick (ra/robot-action-effect-context-schema a) final-s)
	[final-s-context final-s-rew] (find cache-val final-s-context)]
    (println (meta final-s-context))
    (assert (and cache-val (not (= cache-val :in-progress)))) ; Should have been computed
    (if (ra/robot-action-primitive? a) 
        [a]
      (first (sahtn-solution-seq h (:ref (meta final-s-context)) {s 0} final-s)))))
      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Driver  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(derive ::SAHTN-TLA ::ra/RobotHLA)
(defmethod ra/robot-hla-discrete-refinements? ::SAHTN-TLA [a] true)
(defmethod ra/robot-action-precondition-context-schema ::SAHTN-TLA [a] true)
(defmethod ra/robot-action-name ::SAHTN-TLA [a] ['top-level])


(defn sahtn
  [nh initial-plans env sample-depths]
  (let [h {:nh nh :sample-depths sample-depths :cache (HashMap.) :seed (rand-int 100000)}
	tla-type (keyword (str "ros.sahtn/" (name (gensym))))]
    (derive tla-type ::SAHTN-TLA)
    (defmethod ra/robot-hla-refinements tla-type [nh a env] initial-plans)
    (let [tla               {:class tla-type}
	  final-val         (sahtn-result h tla env)
	  [final-s final-r] (last (sort-by val final-val))]
;      (println final-val)
      (println "SAHTN is done evaluating, got best reward" final-r)
      (when final-r
	[(sahtn-solution h tla env final-s) final-r]))))    





(set! *warn-on-reflection* false)



;; (sahtn nh [[(make-gripper-action (make-robot-gripper-state true true))  (make-go-grasp-hla true "bottle2") (make-arm-joint-action (arm-joint-state true "tucked")) (make-go-drop-hla true "bottle2" "table" [16.2 26.5 0.82]) (make-arm-joint-action (arm-joint-state true "tucked")) (make-go-grasp-hla true "bottle") (make-arm-joint-action (arm-joint-state true "tucked")) (make-go-drop-hla true "bottle" "table" [17.8 26.0 0.82]) (make-arm-joint-action (arm-joint-state true "tucked"))]] (get-default-env nh) {:ros.robot-actions/BaseRegionAction 5  :ros.robot-actions/ArmGraspHLA 3  :ros.robot-actions/ArmDropHLA 3  :ros.robot-actions/ArmPoseAction 3})


;[[(make-gripper-action (make-robot-gripper-state true true))  (make-go-grasp-hla true "bottle2") (make-arm-joint-action (arm-joint-state true "tucked")) (make-go-drop-hla true "bottle2" "table" [16.2 26.5 0.82]) (make-grasp-hla true "bottle") (make-arm-joint-action (arm-joint-state true "tucked")) (make-go-drop-hla true "bottle" "table" [17.8 26.0 0.82]) (make-arm-joint-action (arm-joint-state true "tucked"))]]