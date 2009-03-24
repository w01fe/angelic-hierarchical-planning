;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Discrete Road trip
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In this domain, there are a set of locations
; Each location has gas for sale at a (set of) prices
; The goal is to get to the destination while minimizing fuel cost.

(define (domain DISCRETE-ROAD-TRIP)
  (:requirements :strips :typing :equality)
  (:types loc gas price)
  (:predicates 
   (at ?l - loc) 
   (visited ?l - loc)
   (gas ?g - gas)
   (zero ?g - gas)
   (max-gas ?g - gas)
   (road-length ?l1 - loc ?l2 - loc ?l - gas)
   (gas-price ?l - loc ?p - price)
   (one-greater ?g1 - gas ?g2 - gas)
   (geq ?g1 - gas ?g2 - gas)
   (overflow-sum ?g1 - gas ?g2 - gas ?gs - gas)
   (sum ?g1 - gas ?g2 - gas ?gs - gas)
   (median ?g1 - gas ?gm - gas ?g2 - gas)
   )

  (:action get-gas
     :parameters   (?l - loc ?p - price ?cg - gas ?fg - gas)
     :precondition 
       (and (at ?l)
	    (gas-price ?l ?p)
	    (gas ?cg)
	    (one-greater ?fg ?cg))
     :effect 
       (and (not (gas ?cg))
	    (gas ?fg))
     :cost   
       (- ?p))

  (:action drive
     :parameters   (?from - loc ?to - loc ?cg - gas ?len - gas ?fg - gas)
     :precondition 
       (and (at ?from)
	    (gas ?cg)
	    (road-length ?from ?to ?len)
	    (sum ?fg ?len ?cg))
     :effect       
       (and (not (at ?from))
	    (at ?to)
	    (visited ?to)
	    (not (gas ?cg))
	    (gas ?fg))
     :cost  
       0)

  )
