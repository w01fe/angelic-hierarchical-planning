(ns edu.berkeley.ai.angelic.hybrid.ncstrips-descriptions
  (:use edu.berkeley.ai.angelic)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid]
             [linear-expressions :as le]]
	    [edu.berkeley.ai.envs.strips.smart-csps :as smart-csps]
            [edu.berkeley.ai.envs.hybrid-strips :as hs]
            [edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
            [edu.berkeley.ai.angelic.hybrid [dnf-lp-valuations :as hdlv] [continuous-lp-states :as cls]]
            ))


  ; Simple way: split for each combination of applicable forall clauses.
  ; But this may be wasteful, when the yield always resolves true (or is domainted by another effect). 
   ; How do we reduce splits ?????

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Parsing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Effect schemata

(defstruct hybrid-ncstrips-effect-schema :precondition :effect :possible-effect :cost-epxr)

(defn make-hybrid-ncstrips-effect-schema [precondition effect possible-effect cost-expr]
  (struct hybrid-ncstrips-effect-schema precondition effect possible-effect cost-expr))

(defn parse-hybrid-ncstrips-effect-schema [effect discrete-vars predicates numeric-vars numeric-fns const-numeric-fns]
  (util/match [#{[:optional [:precondition    ~pre]]
		 [:optional [:effect          ~eff]]
		 [:optional [:possible-effect ~poss]]
		 [:cost-expr ~cost-expr]}
	       (util/partition-all 2 effect)]
    (util/assert-is (empty? poss))
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
	[discrete-vars numeric-vars] (hybrid/split-var-maps vars discrete-types numeric-types)]
    (make-hybrid-ncstrips-description-schema discrete-vars numeric-vars
      (doall (map #(parse-hybrid-ncstrips-effect-schema % discrete-vars predicates numeric-vars numeric-functions constant-numeric-functions) (next desc))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                   Instantiating
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct hybrid-ncstrips-effect :pos-pres :neg-pres :num-pres :effect :possible-effect :cost-expr)

(defn instantiate-hybrid-effect-schema [schema disc-vars num-vars objects]
  (let [{:keys [precondition effect possible-effect cost-expr]} schema
        all-vars (merge disc-vars num-vars)
        [pos-pres neg-pres num-pres] (hc/split-constraint precondition all-vars objects)
 ;       [adds dels assignments]      (he/get-hybrid-effect-parts effect)
 ;       [poss-adds poss-dels x]      (he/get-hybrid-effect-parts possible-effect)
        ]
;    (assert (empty? x))
    (struct hybrid-ncstrips-effect  pos-pres neg-pres num-pres effect possible-effect cost-expr
;       adds dels poss-adds poss-dels
;       assignments cost-expr
       )))

(defmethod instantiate-description-schema ::HybridNCStripsDescriptionSchema [desc instance]
  (let [{:keys [discrete-vars numeric-vars effects]} desc
        objects (util/safe-get instance :objects)]
    (assoc desc
      :class ::UngroundedHybridNCStripsDescription 
      :objects objects
      :const-fns (util/safe-get instance :constant-numeric-fns)
      :effects (for [e effects] (instantiate-hybrid-effect-schema e discrete-vars numeric-vars objects)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                    Grounding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(derive ::HybridNCStripsDescription :edu.berkeley.ai.angelic/PropositionalDescription)

(defmethod ground-description ::UngroundedHybridNCStripsDescription [schema var-map]
  (let [{:keys [discrete-vars numeric-vars]} schema
        discrete-var-map (util/filter-map (util/keyset discrete-vars) var-map)
        numeric-var-map  (util/filter-map (util/keyset numeric-vars) var-map)]
    (assert (= (count var-map) 
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
  (let [{:keys [pos-pres neg-pres num-pres effect possible-effect cost-expr]} effect
       [adds dels assignments]      (he/get-hybrid-effect-info effect discrete-var-map numeric-var-map constant-fns)
       [poss-adds poss-dels x]      (he/get-hybrid-effect-info possible-effect discrete-var-map numeric-var-map constant-fns)        
        grounder #(props/simplify-atom % discrete-var-map)
        [ground-pos-pres ground-neg-pres ground-adds ground-dels ground-poss-adds ground-poss-dels]
          (map grounder [pos-pres neg-pres adds dels poss-adds poss-dels])
        reward-lm (util/map-vals - (le/hybrid-linear-expr->grounded-lm cost-expr discrete-var-map
                                                                       numeric-var-map constant-fns))]
    (assert (empty? x))
    (when (and (every? clause ground-pos-pres)
               (every? #(not (= :true (clause %))) ground-neg-pres)
               (empty? (util/intersection (set ground-pos-pres) (set ground-neg-pres))))
      (for [[clause clp] 
            (hc/apply-constraint 
             [(reduce #(assoc %1 %2 :true) (apply dissoc clause ground-neg-pres) ground-pos-pres)
              (reduce (fn [c v] (cls/add-lp-state-param c v [] (get reward-lm v))) 
                      clp (vals numeric-var-map))]
             num-pres discrete-var-map numeric-var-map  objects constant-fns 
             (fn [[d c] a] (when (contains? d a) [(assoc d a :true) c]))
             (fn [[d c] a] (when (not (= (d a) :true)) [(dissoc d a) c]))
             (fn [[d c] clm strict?] (when-let [nc (cls/constrain-lp-state-lez c clm strict?)] [d nc]))
             (fn [[d c] clm]         (when-let [nc (cls/constrain-lp-state-eqz c clm)] [d nc]))
             (fn [[d c] clm strict?] (when-let [nc (cls/constrain-lp-state-gez c clm strict?)] [d nc])))]
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






