(ns edu.berkeley.ai.angelic.hybrid.tests.descriptions-and-valuations
  (:use clojure.test edu.berkeley.ai.angelic)
  (:require [edu.berkeley.ai.util :as util] 
            [edu.berkeley.ai.util [propositions :as props] [hybrid :as hybrid]
             [linear-expressions :as le]]
	    [edu.berkeley.ai.envs :as envs]
	    [edu.berkeley.ai.envs.strips.smart-csps :as smart-csps]
            [edu.berkeley.ai.envs.hybrid-strips :as hs]
            [edu.berkeley.ai.envs.hybrid-strips [constraints :as hc] [effects :as he]]
            [edu.berkeley.ai.domains.hybrid-blocks :as hb]
            [edu.berkeley.ai.angelic.hybrid 
             [dnf-lp-valuations :as hdlv]
             [continuous-lp-states :as cls]
             [ncstrips-descriptions :as hnd]]
            ))


(deftest hybrid-descriptions-and-valuations
  ;; Test simple discrete conditions + effects + assignments.  No preconditions.
  (let [dom (hb/make-hybrid-blocks-strips-domain)
        e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
        d1 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips
                [;:precondition
                 :effect (and  [holding x] (= [blockcx x] h))
                 :possible-effect (and [holding x2] (not [gripperempty]))
                 :cost-expr (+ h [blockcx x])]]
              dom '[[block x] [block x2] [y h]])
             e)
        gd1 (ground-description d1 '{x a x2 b h 12.0})
        iv (map->valuation ::hdlv/HybridDNFLPValuation {(envs/get-initial-state e) 1})
        r1  (progress-valuation (progress-valuation iv gd1) gd1)
        [clause lp] (util/safe-singleton (seq (:clause-lp-set r1)))]
    (is (= [:true :unknown :unknown]
           (map clause '[[holding a] [holding b] [gripperempty]])))
    (is (= (valuation-max-reward r1) -37)))
  
  ;; Test use of same variable in two actions.
  (let [dom (hb/make-hybrid-blocks-strips-domain)
        e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
        d1 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips
                [:precondition (and  (= 5 (+ h1 h2)) (< h1 4))
                 :cost-expr (- 0 h1 (* 2 h2))]]
              dom '[[y h1] [y h2]])
             e)
        gd1 (ground-description d1 '{h1 :asdf h2 :foo})
        d2 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips
                [:cost-expr (* -2 h3)]]
              dom '[[y h3]])
             e)
        gd2 (ground-description d2 '{h3 :asdf})
        iv (map->valuation ::hdlv/HybridDNFLPValuation {(envs/get-initial-state e) 0})
        r1  (progress-valuation (progress-valuation iv gd1) gd2)]
    (is (= (valuation-max-reward r1) 14))
    )

  ;; Test simple splitting with multiple effects 
  (let [dom (hb/make-hybrid-blocks-strips-domain)
        e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
        d1 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips [:possible-effect [holding x] :cost-expr 0]]
              dom '[[block x]])
             e)
        gd1 (ground-description d1 '{x a})
        d2 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips
                [:precondition [holding x]
                 :cost-expr 1]
                [:precondition (not [holding x])
                 :cost-expr 2]]
              dom '[[block x]])
             e)
        gd2 (ground-description d2 '{x a})
        iv (map->valuation ::hdlv/HybridDNFLPValuation {(envs/get-initial-state e) 0})
        r1  (progress-valuation (progress-valuation iv gd1) gd2)]
    (is (= (set (map #(vector (get (first %) '[holding a]) (last (cls/solve-lp-state (second %))))
                     (util/safe-get r1 :clause-lp-set)))
           #{[nil -2] [:true -1]}))
    (is (= (valuation-max-reward r1) -1))
    )

  ;; Test numeric stuff
  (let [dom (hb/make-hybrid-blocks-strips-domain)
        e (hb/make-hybrid-blocks-strips-env 6 2 [1 1] '[[a 1 1 2 1] [b 4 1 2 1]] '[[a [[b]]]])
        d1 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips 
                [:precondition (and (>= h 0) (<= h 10))
                 :effect (and (= (blockcx x) h)
                              (= (blockty x) h)
                              (= (blockcx y) 0)
                              (= (blockty y) (* h 0.5))) 
                 :possible-effect [holding x]
                 :cost-expr h]
                [:precondition (and (>= h 0) (<= h 5))
                 :effect (and (= (blockcx x) (- 1 (* 2 h)))
                              (= (blockcx y) h)
                              (= (blockty y) h))  
                 :possible-effect [holding y]
                 :cost-expr (* 2 h)]]
              dom '[[block x] [block y] [x h]])
             e)
        gd1 (ground-description d1 '{x a y b h :height})
        d2 (instantiate-description-schema
             (parse-description
              '[:hybrid-ncstrips
                [:precondition (and (forall (e - block) (>= (blockcx e) 6) (<= (blockty e) 7))) 
                 :cost-expr (* 4 (- 0 [blockty x] [blockty y]))]]
              dom '[[block x] [block y]])
             e)
        gd2 (ground-description d2 '{x a y b})
        iv (map->valuation ::hdlv/HybridDNFLPValuation {(envs/get-initial-state e) 0})
        r1  (progress-valuation (progress-valuation iv gd1) gd2)]
    (is (= (set (map #(vector (get (first %) '[holding a]) (last (cls/solve-lp-state (second %))))
                     (util/safe-get r1 :clause-lp-set)))
           #{[:unknown 30] [:unknown 35] [nil 14]}))))








