(ns edu.berkeley.ai.angelic.hierarchies.cfg-hierarchies
  (:refer-clojure)
  (:use edu.berkeley.ai.util edu.berkeley.ai.angelic.hierarchies)
  )

(derive ::CFGHLA ::HLA)

(defstruct cfg-hla :class :nonterminal :production-rules :terminal-map) 

(defn make-cfg-hla [NT production-rules terminal-map]
  (assert-is (distinct-elts? (concat (keys production-rules) (keys terminal-map))))
  (struct cfg-hla ::CFGHLA NT production-rules terminal-map))

(derive ::TerminalCFGHLA ::PrimitiveHLA)

(defstruct terminal-cfg-hla :class :primitive)

(defn make-terminal-cfg-hla [prim-act]
  (struct terminal-cfg-hla ::TerminalCFGHLA prim-act))



(defmethod hla-name ::CFGHLA [hla] (:name hla))

(defmethod hla-immediate-refinements [::CFGHLA ::Valuation] [hla opt-val]
  (for [production (get (:production-rules hla) (:nonterminal hla))]
    (for [element production]
      (if-let [prim (get (:terminal-map hla) element)]
	  (make-terminal-cfg-hla prim)
        (make-cfg-hla element (:production-rules hla) (:terminal-map hla))))))

(defmethod hla-hierarchical-preconditions ::CFGHLA [hla]
  nil)

(defmethod hla-optimistic-description     ::CFGHLA [hla]
  (throw (UnsupportedOperationException. "TODO")))

(defmethod hla-pessimistic-description    ::CFGHLA [hla]
  (throw (UnsupportedOperationException. "TODO")))



(comment 

(let [its (iterate #(subvec % 0 10) (apply vector (range 20)))] 
  (doseq [i (range 0 100 10)] 
    (print i " ")
    (let [sub (nth its i)]
      (time (dotimes [_ 1000000] (sub 5))))))

)