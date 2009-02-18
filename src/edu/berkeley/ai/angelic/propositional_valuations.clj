(in-ns 'edu.berkeley.ai.angelic)


(derive ::PropositionalValuation ::Valuation)

(defmulti #^{:doc "Compute the a seq of [true poss] maps from pred-name ==> possibly-true atom"}
  valuation->pred-maps :class)


      