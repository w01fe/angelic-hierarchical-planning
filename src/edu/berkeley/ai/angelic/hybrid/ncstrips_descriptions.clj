(ns edu.berkeley.ai.angelic.hybrid.ncstrips-descriptions
  (:use edu.berkeley.ai.angelic edu.berkeley.ai.angelic.hybrid)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid-util]
             [linear-expressions :as le]]
	    [edu.berkeley.ai.envs.strips.smart-csps :as smart-csps]
            [edu.berkeley.ai.envs.hybrid-strips :as hs]
            [edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
            [edu.berkeley.ai.angelic.hybrid :as hybrid]
            [edu.berkeley.ai.angelic.hybrid [dnf-lp-valuations :as hdlv] [continuous-lp-states :as cls]]
            ))


  ; Simple way: split for each combination of applicable forall clauses.
  ; But this may be wasteful, when the yield always resolves true (or is domainted by another effect). 
   ; How do we reduce splits ?????

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Parsing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Effect schemata

(defstruct hybrid-ncstrips-effect-schema :precondition :effect :possible-effect :cost-expr)

(defn make-hybrid-ncstrips-effect-schema [precondition effect possible-effect cost-expr]
  (struct hybrid-ncstrips-effect-schema precondition effect possible-effect cost-expr))

(defn parse-hybrid-ncstrips-effect-schema [effect discrete-vars predicates numeric-vars numeric-fns const-numeric-fns]
  (util/match [#{[:optional [:precondition    ~pre]]
		 [:optional [:effect          ~eff]]
		 [:optional [:possible-effect ~poss]]
		 [:cost-expr ~cost-expr]}
	       (util/partition-all 2 effect)]
    (make-hybrid-ncstrips-effect-schema
     (hc/parse-and-check-constraint pre discrete-vars predicates numeric-vars numeric-fns const-numeric-fns)
     (he/parse-and-check-effect eff discrete-vars predicates numeric-vars numeric-fns const-numeric-fns)
     (he/parse-and-check-effect poss discrete-vars predicates numeric-vars numeric-fns const-numeric-fns)
     (le/parse-and-check-hybrid-linear-expression cost-expr discrete-vars numeric-vars numeric-fns const-numeric-fns))))
     

;; Description schemata

(defstruct hybrid-ncstrips-description-schema :class :discrete-vars :numeric-vars  :effects)
(defn make-hybrid-ncstrips-description-schema [discrete-vars numeric-vars effects]
    (struct hybrid-ncstrips-description-schema ::HybridNCStripsDescriptionSchema 
	    discrete-vars numeric-vars effects))

(defmethod parse-description :hybrid-ncstrips [desc domain vars]  
  (util/assert-is (isa? (:class domain) ::hs/HybridStripsPlanningDomain))
  (let [{:keys [discrete-types numeric-types predicates numeric-functions constant-numeric-functions]} domain
	[discrete-vars numeric-vars] (hybrid-util/split-var-maps vars discrete-types numeric-types)]
    (make-hybrid-ncstrips-description-schema discrete-vars numeric-vars
      (doall (map #(parse-hybrid-ncstrips-effect-schema % discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions) (next desc))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Instantiating
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct hybrid-ncstrips-effect :pos-pres :neg-pres :num-pres :effect :possible-effect :cost-expr)

(defn instantiate-hybrid-effect-schema [schema objects]
  (let [{:keys [precondition effect possible-effect cost-expr]} schema
;        all-vars (merge disc-vars num-vars)
        [pos-pres neg-pres num-pres] (hc/split-constraint precondition {} objects)]
    (struct hybrid-ncstrips-effect  pos-pres neg-pres num-pres effect possible-effect cost-expr)))

(defmethod instantiate-description-schema ::HybridNCStripsDescriptionSchema [desc instance]
  (assoc desc
    :class ::UngroundedHybridNCStripsDescription 
    :objects  (util/safe-get instance :objects)
    :constant-fns (util/safe-get instance :constant-numeric-vals)
    :effects (doall  
              (for [e (util/safe-get desc :effects)] 
                (instantiate-hybrid-effect-schema e (util/safe-get instance :objects))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    Grounding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::HybridNCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)

;; Var-map can for cont vars point at either: number, or unique LP-var symbol.

(defmethod ground-description ::UngroundedHybridNCStripsDescription [schema var-map]
  (let [{:keys [discrete-vars numeric-vars]} schema
        discrete-var-map (util/restrict-map var-map (keys discrete-vars))
        numeric-var-map  (util/restrict-map var-map (keys numeric-vars))]
;    (println var-map discrete-vars numeric-vars)
    (util/assert-is (= (count var-map) 
                       (+ (count discrete-vars) (count numeric-vars))
                       (+ (count discrete-var-map) (count numeric-var-map))))
    (assoc schema 
      :class ::HybridNCStripsDescription 
      :discrete-var-map discrete-var-map 
      :numeric-var-map numeric-var-map)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    Applying
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defn progress-clause-lp-pair [[clause clp] effect discrete-var-map numeric-var-map objects constant-fns]
  (assert constant-fns)
  (let [{:keys [pos-pres neg-pres num-pres effect possible-effect cost-expr]} effect
       [adds dels assignments]      (he/get-hybrid-effect-info effect discrete-var-map numeric-var-map constant-fns)
       [poss-adds poss-dels x]      (he/get-hybrid-effect-info possible-effect discrete-var-map numeric-var-map constant-fns)        
;               _ (println pos-pres neg-pres num-pres effect possible-effect cost-expr adds dels assignments poss-adds poss-dels x)
        grounder #(props/simplify-atom discrete-var-map %) 
        ground-pos-pres (map grounder pos-pres)
        ground-neg-pres (map grounder neg-pres)
        reward-lm (util/map-vals - (le/hybrid-linear-expr->grounded-lm cost-expr discrete-var-map
                                                                       numeric-var-map constant-fns))]
;    (println reward-lm)
;    (println pos-pres neg-pres ground-pos-pres ground-neg-pres clause)
    (assert (empty? x))
    (when (and (every? clause ground-pos-pres)
               (every? #(not (= :true (clause %))) ground-neg-pres)
               (empty? (util/intersection (set ground-pos-pres) (set ground-neg-pres))))
;      (println num-pres)
      (for [[clause clp] 
            (hc/apply-constraint 
             [(reduce #(assoc %1 %2 :true) (apply dissoc clause ground-neg-pres) ground-pos-pres)
              (reduce (fn [c v] (if (number? v) c (cls/add-lp-state-param c v [] (get reward-lm v)))) 
                      clp (vals numeric-var-map))]
             num-pres discrete-var-map numeric-var-map  objects constant-fns 
             (fn [[d c] a] (when (contains? d a) [(assoc d a :true) c]))
             (fn [[d c] a] (when (not (= (d a) :true)) [(dissoc d a) c]))
             (fn [[d c] clm strict?] (when-let [nc (cls/constrain-lp-state-lez c clm strict?)] [d nc]))
             (fn [[d c] clm]         (when-let [nc (cls/constrain-lp-state-eqz c clm)] [d nc]))
             (fn [[d c] clm strict?] (when-let [nc (cls/constrain-lp-state-gez c clm strict?)] [d nc]))
             (fn [[d c]] (cls/lp-state-feasible? c)))]
        [(reduce #(assoc %1 %2 :unknown)
                 (reduce #(assoc %1 %2 :true) (apply dissoc clause dels) adds)
                 (concat (filter #(nil? (clause %)) poss-adds)
                                    (filter #(= :true (clause %)) poss-dels)))         
         (cls/update-lp-state clp assignments reward-lm)]))))

(defmethod progress-valuation [::hdlv/HybridDNFLPValuation ::HybridNCStripsDescription] [val desc]
  (let [{:keys [discrete-var-map numeric-var-map effects objects constant-fns]} desc]
    (hdlv/make-hybrid-dnf-lp-valuation
     (apply concat 
            (for [clause-lp-pair (util/safe-get val :clause-lp-set)
                  effect         effects]
              (progress-clause-lp-pair clause-lp-pair effect discrete-var-map numeric-var-map objects constant-fns))))))


(defmethod progress-valuation    [::hdlv/HybridDNFLPValuation ::hybrid/HybridFinishDescription] [val desc]
  (let [[pos neg num] (hc/split-constraint (util/safe-get (:goal desc) :constraint)
                                           {} (util/safe-get desc :objects))
        result (progress-valuation val
                 (assoc desc 
                   :class ::HybridNCStripsDescription 
                   :effects [{:pos-pres pos :neg-pres neg :num-pres num}]))]
    (if (empty-valuation? result) *pessimal-valuation*
      (make-hybrid-finish-valuation (valuation-max-reward val) result))))





