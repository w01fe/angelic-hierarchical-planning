;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Discrete Road trip
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In this domain, there are a set of locations
; Each location has gas for sale at a (set of) prices
; The goal is to get to the destination while minimizing fuel cost.

(define (domain DISCRETE-ROAD-TRIP)
  (:requirements :strips :typing :equality)
  (:types loc gas)
  (:predicates 
   (at ?l - loc) 
   (visited ?l - loc)
   (gas ?g - gas)
   (zero ?g - gas)
   (max-gas ?g - gas)
   (road-length ?l1 - loc ?l2 - loc ?l - gas)
   (has-gas1 ?l - loc)
   (has-gas2 ?l - loc)
   (has-gas3 ?l - loc)
   (one-greater ?g1 - gas ?g2 - gas)
   (geq ?g1 - gas ?g2 - gas)
   (overflow-sum ?g1 - gas ?g2 - gas ?gs - gas)
   (sum ?g1 - gas ?g2 - gas ?gs - gas)
   (median ?g1 - gas ?gm - gas ?g2 - gas)
   )

  (:action get-gas1
     :parameters   (?l - loc ?cg - gas ?fg - gas)
     :precondition 
       (and (at ?l)
	    (has-gas1 ?l)
	    (gas ?cg)
	    (one-greater ?fg ?cg))
     :effect 
       (and (not (gas ?cg))
	    (gas ?fg))
     :cost   
       1)

  (:action get-gas2
     :parameters   (?l - loc ?cg - gas ?fg - gas)
     :precondition 
       (and (at ?l)
	    (has-gas2 ?l)
	    (gas ?cg)
	    (one-greater ?fg ?cg))
     :effect 
       (and (not (gas ?cg))
	    (gas ?fg))
     :cost   
       2)

  (:action get-gas3
     :parameters   (?l - loc ?cg - gas ?fg - gas)
     :precondition 
       (and (at ?l)
	    (has-gas3 ?l)
	    (gas ?cg)
	    (one-greater ?fg ?cg))
     :effect 
       (and (not (gas ?cg))
	    (gas ?fg))
     :cost   
       3)

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
