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

  )








