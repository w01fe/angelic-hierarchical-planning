(in-ns 'edu.berkeley.ai.angelic)


(derive ::PropositionalValuation ::Valuation)

(defmulti #^{:doc "Compute the set of mappings consistent with this valuation and condition, where dummy-domains maps variables to allowed domains"}
  valuation-consistent-mappings (fn [val cond dummy-domains] [(:class val) (:class cond)]))


      